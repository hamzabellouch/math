import Mathlib

namespace OAI

   
                                                                         
                                                                

                                                                          
                                                                         
                                                                        
                                                                      
  
namespace MinUncutGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end MinUncutGames.BinaryFormula

namespace MinUncutGames.BinaryEncoding
open BinaryFormula

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def nameBits (name : Nat) : List Bool := frame name.bits

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

end MinUncutGames.BinaryEncoding

namespace MinUncut
open MinUncutGames.BinaryFormula MinUncutGames.BinaryEncoding

                                                                        
                                                                           
structure Output where
  vertices : ℕ
  adjacent : Fin vertices → Fin vertices → Bool
  symmetric : ∀ u v, adjacent u v = adjacent v u
  loopless : ∀ u, adjacent u u = false
  threshold : ℕ
  threshold_pos : 1 ≤ threshold

                                                                              
                                                           
def Output.uncut (G : Output) (cut : Fin G.vertices → Bool) : ℕ :=
  (Finset.univ.filter fun uv : Fin G.vertices × Fin G.vertices =>
    uv.1 < uv.2 ∧ G.adjacent uv.1 uv.2 = true ∧ cut uv.1 = cut uv.2).card

                                                                             
                                     
noncomputable def Output.opt (G : Output) : ℕ :=
  (Finset.univ.image G.uncut).min' (by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)

                                                                        
                                                                           
def Output.bits (G : Output) : List Bool :=
  nameBits G.vertices ++
    ((List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => G.adjacent u v) ++
    nameBits G.threshold

                                                                               
                                                             
def inputBits (input : ℕ × Formula) : List Bool :=
  nameBits input.1 ++ formulaBits input.2

                                                                            
                                                                         
                                                                       
                                                                 
structure Reduction where
  reduce : ℕ → Formula → Output
  machine : Turing.TM2Computable inputBits Output.bits (fun p => reduce p.1 p.2)
  finiteAlphabet : ∀ k : machine.tm.K, Finite (machine.tm.Γ k)
  time : ℕ → Polynomial ℕ
  runtime : ∀ K φ,
    Turing.TM2OutputsInTime machine.tm
      ((inputBits (K, φ)).map machine.inputAlphabet.symm)
      (some (((reduce K φ).bits).map machine.outputAlphabet.symm))
      ((time K).eval (formulaBits φ).length)
  size : ℕ → Polynomial ℕ
  output_size : ∀ K φ,
    (reduce K φ).vertices + (reduce K φ).bits.length ≤
      (size K).eval (formulaBits φ).length
  yes : ∀ K, 2 ≤ K → ∀ φ, φ.Satisfiable →
    (reduce K φ).opt ≤ (reduce K φ).threshold
  no : ∀ K, 2 ≤ K → ∀ φ, ¬ φ.Satisfiable →
    K * (reduce K φ).threshold < (reduce K φ).opt

end MinUncut

namespace MinUncut

theorem main : Nonempty Reduction := by
  sorry

end MinUncut

end OAI
