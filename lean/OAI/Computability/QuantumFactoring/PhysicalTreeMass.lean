import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalTreeMachine

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RecordedHistory
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Filtering the actual chronological query at each clock tick. No collection
of answers for unselected/counterfactual moduli occurs in this predicate. -/
noncomputable def passed (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>passed x t h.1 ∧ NodeKernel.passed (M.query.eval (M.config x t h.1)) h.2

lemma state_normalized (x : Basis c) (t : ℕ) :
    ∑ h,Complex.normSq (M.state x t h)=1 := by
  induction t with
  | zero=>simp [state,Trace]
  | succ t ih=>
    change ∑ h,Complex.normSq (appendState (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))) h)=1
    exact append_normalized _ _ ih (fun h=>NodeKernel.fresh_normalized _)

/-- Exact physical-history probability for a clocked network controller. This
is unconditional in its update network and retains all quantum scratch. -/
theorem passed_mass (hn : 128≤n) (x : Basis c) (t : ℕ) :
    outcomeMass (M.passed x t) (M.state x t)=
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))^t := by
  induction t with
  | zero=>simp [outcomeMass,passed,state,Trace]
  | succ t ih=>
    change outcomeMass (fun h : Trace n t×NodeKernel.Raw n=>M.passed x t h.1 ∧
      NodeKernel.passed (M.query.eval (M.config x t h.1)) h.2)
      (appendState (M.state x t) (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))))=_
    rw [append_constant_mass (M.state x t)
      (fun h=>NodeKernel.fresh (M.query.eval (M.config x t h))) (M.passed x t)
      (fun h=>NodeKernel.passed (M.query.eval (M.config x t h)))
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))
      (fun h _=>NodeKernel.passed_mass hn (M.query.eval (M.config x t h))),ih]
    exact (pow_succ (((Completion.target n:ℝ)^(n^5+1))^(2*n)) t).symm

/-- The on-support passing event in the retained concrete physical registers.
An efficient retrospective Boolean validator is still needed before using it as
a circuit-controlled phase; this definition does not provide one by fiat. -/
noncomputable def physicalPassed (x : Basis c) (t : ℕ) (z : Basis (M.width t)) : Prop :=
  ∃ h,M.encoded x t h=z ∧ M.passed x t h

lemma physicalPassed_encoded (x : Basis c) (t : ℕ) (h : Trace n t) :
    M.physicalPassed x t (M.encoded x t h) ↔ M.passed x t h := by
  constructor
  · rintro ⟨a,ha,hp⟩
    exact (M.encoded_injective x t ha) ▸ hp
  · exact fun hp=>⟨h,rfl,hp⟩

theorem program_passed_mass (hn : 128≤n) (x : Basis c) (t : ℕ) :
    outcomeMass (M.physicalPassed x t)
      ((programMatrix (M.program t)).mulVec (basisVector (M.initial t x)))=
      (((Completion.target n:ℝ)^(n^5+1))^(2*n))^t := by
  rw [M.program_state,outcomeMass_encode _ (M.encoded_injective x t)]
  have he : M.physicalPassed x t ∘ M.encoded x t=M.passed x t := by
    funext h
    exact propext (M.physicalPassed_encoded x t h)
  rw [he]
  exact M.passed_mass hn x t

end NodeMachine
end ExactQuantumFactoring


end

end OAI
