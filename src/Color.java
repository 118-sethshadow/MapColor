/*
 * Programmer: Kartikeya Kaushal
 * Class: CS 201
 * Lecturer: John Lillis
 * Project 2 Part 3: Color program
 */


import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Scanner;

import org.sat4j.core.*;
import org.sat4j.minisat.*;
import org.sat4j.specs.*;


public class Color {
	
	
	public static Scanner cover (String fName) throws FileNotFoundException {
		  return new Scanner (new FileInputStream(fName));
		}
	
	// writes to output file
	public static PrintStream write(String fName) throws FileNotFoundException {
	  return new PrintStream(new FileOutputStream(fName));
	}
	
	
	public static void main(String[] args){
		
		//make sure the three cmd line requirements are inputed
		if(args.length != 3) {
	        System.out.println("Must specify map file, # of colors, and coloring file");
	        System.exit(0);
		}
		
		//parse the number value from cmd line
		int maxColors = Integer.parseInt(args[1]);
		
		if(maxColors == 1){
			System.out.println("You can't color a border with only 1 color!");
			System.exit(0);
	}
		
		//declare scanner
		Scanner border = null;
		PrintStream colorer = null;
		
		//declare arraylists to use
		ArrayList<Border> borders = new ArrayList<Border>();
		ArrayList <String> region = new ArrayList <String>();
		ArrayList <String> colors = new ArrayList <String>(); 
		ArrayList <Integer> truth = new ArrayList<Integer>();


		//set an instant of class Color
		Color doIt = new Color();
		
		try{
		
		//read the border assignments
		border = cover(args[0]);
		doIt.readTheBorders(border, borders, region);
		//System.out.println(borders.size());
		//System.out.println(region.size());
				
		//Make a CNF clause for the input file and see if can be colored with k colors
		doIt.checkValidity(region, borders, maxColors, truth);
		
		//write the output file
        colorer = write(args[2]);
        //assign the colors and then write them and the regions to the file
        doIt.assignColors(colorer, maxColors, colors, truth, region);

		}
		catch(FileNotFoundException e) {
	        System.out.println("Error with an input file");
	        System.exit(0);
	    }
		
	}//end main
	
/***************************************************Methods for reading and checking********************************************************/
	
	
	private static class Border{
		String r1;
		String r2;
		
		public Border(String region1, String region2){
			r1 = region1;
			r2 = region2;
		}
		public String region1(){
			return r1;
		}
		public String region2(){
			return r2;
		}
	}
	
	//read the input file on the cmd line
	public void readTheBorders(Scanner reader, ArrayList<Border> borders, ArrayList<String> region){
					
			
			//read the file line by line
			while (reader.hasNext()){
				Scanner lr = new Scanner(reader.nextLine());
				String s1 = lr.next();
				String s2 = lr.next().trim();
			//get every region and put into an arraylist
			if(!region.contains(s1))
				region.add(s1);
			if(!region.contains(s2))
				region.add(s2);
			
			//add each border to arraylist
			borders.add(new Border(s1, s2));
			//System.out.println(s1 + " " + s2);
			}
			

			//for(int r = 0; r < region.size(); r++){
			//	System.out.println(region.get(r));
			//}
			
			//close scanner
			reader.close();
		
		
	}//end readTheBorders
	
	
	//use sat4j to determine if coloring scheme is valid
	public void checkValidity(ArrayList<String> regions, ArrayList<Border> borders, int k,	ArrayList <Integer> truth){
		
		int n = regions.size();
		
		int[] holder = new int[k];
		int[] clause2 = new int[2];
		
		ISolver solver = SolverFactory.newDefault();
        solver.newVar(100);
        
        	try {
            	
        		 
        	    for(int r = 0; r < n; r++){
        	    	//add the existence clauses to determine a color exists for each region
        	       	for (int v = 1; v <= k; v++){
        	        	holder[v-1] = v + k*r;
        	        }//end existence
                     solver.addClause(new VecInt(holder));

             	    //add the AT MOST ONE clauses to prevent a state from having more than 1 color
                     for(int b = 1; b < k ; b++){
                    	 //System.out.println("region");
                    	 for(int c = 0; c < k; c++){
         	    		clause2[0] = (holder[b]-1)*(-1);
         	    		clause2[1] = holder[c]*(-1);
         	    		
         	    		if(clause2[1] < clause2[0]){
         	    			solver.addClause(new VecInt(clause2));
         	    		//System.out.println(clause2[0] + " " + clause2[1]);
         	    			}
                    	 }
         	    	
         	    	}//end AT MOST ONE
        	      }//end outer for loop
        	    
        	  //add clauses to make sure adjacent states are not the same color
        	 
        	    for(Border together: borders){
        	    	
        	    	//System.out.println(together.region1() + " " + together.region2());
        	    	String[] pair = new String[2];
        	    	pair[0]= together.region1();
        	    	pair[1]= together.region2();
        	    	int position = regions.lastIndexOf(pair[0]);
        	    	int position2 = regions.lastIndexOf(pair[1]);
        	    	//System.out.println(position + " " + position2);
        	    	for(int e = 1; e<=k; e++){
        	    		clause2[0]=((position*k)+e)*(-1);
        	    		clause2[1]=((position2*k)+e)*(-1);
        	    		solver.addClause(new VecInt(clause2));
        	    		//System.out.println(clause2[0] + " " + clause2[1]);   
        	    		}
        	    	
        	    }//end adjacent check
        	    
        	    
                // Now let's see if it is satisfiable
                if(solver.isSatisfiable()){
                	int [] lits = solver.model(); 
                								  
                	//System.out.println("Satisfying truth assignment:");
                	//System.out.println(Arrays.toString(lits));
                	
                	for(int g = 0; g<lits.length; g++){
                		truth.add(lits[g]);
                	}
                }
                else{
                	System.out.println("  Map cannot be colored with these parameters");
                	System.exit(0);
                }
            }
            catch(Exception e){}
        
		
	}

	
	public void assignColors(PrintStream given, int k, ArrayList<String> colors, ArrayList<Integer> truth, ArrayList<String> regions){
		
		String value = "COLOR";
		int n = regions.size();

		
		//make the colors
		for (int i = 1; i <= k; i ++){
			value = "COLOR" + i;
			colors.add(value);
			//System.out.println(value);
		}//end make the colors loop
		
		//now assign these colors to the states based on the truth assignment
		for(int j = 0; j < n; j++){
			String state = regions.get(j);
			int position = regions.lastIndexOf(state);
			//System.out.println("region");
			for(int l = 1; l <= k; l++){
				int give = ((position*k)+l);
				//System.out.println(give);
				//System.out.println(truth.get((l-1)+k*j));
				if(give == truth.get((l-1)+k*j)){
					given.println(state + " " + colors.get(l-1));
				}
					
			}
		}//end assigning the colors
		System.out.println("wrote the color assignments for given parameters");
	}//end assignColors
	
}//end Color