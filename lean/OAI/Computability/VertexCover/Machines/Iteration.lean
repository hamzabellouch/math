import Mathlib
import OAI.Computability.VertexCover.Machines.NatLog
import OAI.Computability.VertexCover.Machines.LoopFrom
import OAI.Computability.VertexCover.Machines.Round
import OAI.Computability.VertexCover.Machines.TableCodeBound
import OAI.Computability.VertexCover.Machines.InitialCorrect

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                     
section

namespace VertexCover.Machine
open UniqueGames.Foundations
open PCP
 theorem Iterate.run_source {α : Type} (f : α → α) (n : ℕ) (a : α) :
    Iterate.run f n a = AmplificationIteration.run f n a := by
  have commute (k : ℕ) (a : α) :
      AmplificationIteration.run f k (f a) = f (AmplificationIteration.run f k a) := by
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg f ih
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact (ih (f a)).trans (commute n a)
namespace IterationMachine
open TableMachine
abbrev State := ℕ × GraphTables.Table
abbrev enc : State → List Bool := prodBits natBits tableCode

def initial (F : Target.Formula) : State :=
  (TableIteration.iterationCount F,RawInitialTables.table F)
def result (H : RoundTables.BaseTable) (F : Target.Formula) : State :=
  (0,TableIteration.outputTable H F)

noncomputable def sizePolynomial : Polynomial ℕ :=
  let s := (2*Polynomial.X)^TableIteration.polynomialDegree*Polynomial.X
  2*Polynomial.X+1+TableMachine.lengthPolynomial.comp s

 theorem size_bound (H : RoundTables.BaseTable) (F : Target.Formula) (k l : ℕ)
    (h : k+l=TableIteration.iterationCount F) :
    (enc (l,Iterate.run (RoundTables.build H) k (RawInitialTables.table F))).length ≤
      sizePolynomial.eval (enc (initial F)).length := by
  let s := RoundTables.size (RoundTables.initial F)
  let N := (enc (initial F)).length
  have hsN : s ≤ N := by
    have hs := TableMachine.size_le_code (RawInitialTables.table F)
    simp only [N,initial,pairBits_length,natBits_length]
    exact hs.trans (Nat.le_add_left _ _)
  have hlN : l ≤ N := by
    simp only [N,initial,pairBits_length,natBits_length]
    omega
  have hk : k ≤ AmplificationIteration.rounds s := by
    change k ≤ TableIteration.iterationCount F
    omega
  have hp := (Nat.pow_le_pow_right RoundTables.sizeFactor_positive hk).trans
    (AmplificationIteration.blowup_rounds_le (RoundTables.size_positive (RoundTables.initial F))
      TableIteration.sizeFactor_le_power)
  have ht := (TableIteration.run_size H k (RoundTables.initial F)).trans (Nat.mul_le_mul_right s hp)
  have htN := ht.trans (Nat.mul_le_mul
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hsN) _) hsN)
  have hm : (Iterate.run (RoundTables.build H) k (RawInitialTables.table F)).vertices+
      (Iterate.run (RoundTables.build H) k (RawInitialTables.table F)).darts ≤
      (2*N)^TableIteration.polynomialDegree*N := by
    rw [Iterate.run_source]
    change (TableIteration.runTables H k (RawInitialTables.table F)).vertices+
      (TableIteration.runTables H k (RawInitialTables.table F)).darts ≤ _
    have hv : (TableIteration.run H k (RoundTables.initial F)).val =
        TableIteration.runTables H k (RawInitialTables.table F) := TableIteration.run_val H k _
    rw [← hv]
    exact htN
  have hb := (TableMachine.codeLength_le_eval _).trans
    (Complexity.MachineComposition.natPolynomial_eval_mono _ hm)
  calc
    _ = 2*l+1+(tableCode (Iterate.run (RoundTables.build H) k (RawInitialTables.table F))).length := by
      simpa only [natBits_length] using pairBits_length (natBits l) (tableCode (Iterate.run (RoundTables.build H) k (RawInitialTables.table F)))
    _ ≤ 2*N+1+TableMachine.lengthPolynomial.eval ((2*N)^TableIteration.polynomialDegree*N) :=
      Nat.add_le_add (by omega) hb
    _ = sizePolynomial.eval N := by
      simp only [sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp,Polynomial.eval_pow]

noncomputable def initialPoly : Poly FormulaParser.targetCode enc initial := by
  let T := InitialTable.initialPoly
  let s := ((T.comp TableMachine.verticesPoly).pair (T.comp TableMachine.dartsPoly)).comp Poly.natAdd
  let n := (s.comp Poly.natLog2).comp Poly.natSucc
  exact (n.pair T).congr (fun _ => rfl)

noncomputable def loopPoly (H : RoundTables.BaseTable) :
    Poly (fun F => enc (initial F)) enc (result H) :=
  Poly.loopFrom (Iterate.bodyPoly (RoundTables.build H) tableCode (RoundMachine.poly H))
    initial (result H) sizePolynomial (Polynomial.X+1) (by
      intro F
      refine ⟨TableIteration.iterationCount F+1,?_,?_⟩
      · simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,initial,
          prodBits,pairBits_length,natBits_length]
        omega
      · have h := Iterate.bounded (RoundTables.build H) tableCode (TableIteration.iterationCount F)
          (RawInitialTables.table F) _ (size_bound H F)
        simpa only [Iterate.run_source,initial,result,TableIteration.outputTable,TableIteration.runTables] using h)
noncomputable def poly (H : RoundTables.BaseTable) :
    Poly FormulaParser.targetCode tableCode (TableIteration.outputTable H) :=
  ((Poly.initializeLoop initialPoly (loopPoly H)).comp (Poly.snd natBits tableCode)).congr (fun _ => rfl)
end IterationMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
