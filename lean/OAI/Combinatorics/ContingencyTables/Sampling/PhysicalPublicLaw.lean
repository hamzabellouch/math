import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalEventBounds
import OAI.Combinatorics.ContingencyTables.AlgorithmStatements

namespace OAI

/-! # Public probabilities and physical terminal events -/

namespace ContingencyTables.PhysicalPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds
open scoped BigOperators Classical
noncomputable section

def outputs {Q : Type} (as : List Symbol) (d : Cfg Symbol Q) : Prop :=
  d.state=none ∧ d.tape.right₀=ListBlank.mk as

lemma tableMass_eq (P : Program) (input : List Symbol) (t : ℕ)
    {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    Algorithms.tableMass P.machine input t X=
      ((experiment P.table t (P.initial (Tape.mk₁ input))).mean
        (event (outputs (Algorithms.encodeMatrix X))):ℝ) := by
  have he : ∀ b : Bits t,Algorithms.OutputsTable P.machine input b X ↔
      outputs (Algorithms.encodeMatrix X)
        (execute P.table t (P.initial (Tape.mk₁ input)) (extend b)) := by
    intro b
    simp only [Algorithms.OutputsTable,outputs,run_halted_iff,Program.run_tape]
  have hm := physical_law P.table t (P.initial (Tape.mk₁ input))
    (event (outputs (Algorithms.encodeMatrix X)))
  have ha : average (fun b : Bits t => event (outputs (Algorithms.encodeMatrix X))
      (execute P.table t (P.initial (Tape.mk₁ input)) (extend b)))=
      ((Finset.univ.filter fun b : Bits t => Algorithms.OutputsTable P.machine input b X).card:ℚ)/
        (2:ℚ)^t := by
    simp only [average,event,←he,Finset.sum_boole]
  rw [ha] at hm
  have hc := congrArg (fun x : ℚ => (x:ℝ)) hm
  simpa only [Algorithms.tableMass,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using hc

lemma haltMass_eq (P : Program) (input : List Symbol) (t : ℕ) :
    Algorithms.haltMass P.machine input t=
      ((experiment P.table t (P.initial (Tape.mk₁ input))).mean
        (event (fun d => d.state=none)):ℝ) := by
  have hm := physical_law P.table t (P.initial (Tape.mk₁ input))
    (event (fun d => d.state=none))
  have ha : average (fun b : Bits t => event (fun d => d.state=none)
      (execute P.table t (P.initial (Tape.mk₁ input)) (extend b)))=
      ((Finset.univ.filter fun b : Bits t => (MatchingFPRAS.run P.machine input b).state=none).card:ℚ)/
        (2:ℚ)^t := by
    simp only [average,event,←run_halted_iff,Finset.sum_boole]
  rw [ha] at hm
  have hc := congrArg (fun x : ℚ => (x:ℝ)) hm
  simpa only [Algorithms.haltMass,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using hc

lemma tail_eq (P : Program) (input : List Symbol) (t : ℕ) :
    1-Algorithms.haltMass P.machine input t=
      PhysicalRetryTail.tail P.table (P.initial (Tape.mk₁ input)) t := by
  rw [haltMass_eq]
  have he : event (fun d : Cfg Symbol P.State => d.state=none)=
      fun d => 1-PhysicalRetryTail.live d := by
    funext d
    unfold event PhysicalRetryTail.live
    split_ifs <;> norm_num
  rw [he,mean_one_sub]
  simp only [Rat.cast_sub,Rat.cast_one,PhysicalRetryTail.tail]
  ring

end
end ContingencyTables.PhysicalPublicLaw

end OAI
