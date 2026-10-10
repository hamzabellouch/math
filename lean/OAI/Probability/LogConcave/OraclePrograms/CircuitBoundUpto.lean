import Mathlib
import OAI.Probability.LogConcave.JetEstimates.WireStep

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.TensorEnergy
open scoped BigOperators

lemma circuit_bound_upto {D : ℕ → Type*} [∀k,Fintype (D k)] [DecidableEq (D 0)]
    (A : ∀k,D (k+1) → D k → ℝ) (C : ℕ → ℝ) (n : ℕ)
    (hC : ∀k<n,0≤C k) (hA : ∀k<n,Bound (A k) (C k)) :
    Bound (circuit A n) (∏k∈Finset.range n,C k) := by
  induction n with
  | zero => simpa only [circuit,Finset.range_zero,Finset.prod_empty] using (bound_identity (I:=D 0))
  | succ n ih =>
    have hi := ih (fun k hk => hC k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      (fun k hk => hA k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    simpa only [circuit,Finset.prod_range_succ,mul_comm] using
      (hA n (Nat.lt_succ_self n)).comp hi (hC n (Nat.lt_succ_self n))

theorem closed_wire_circuit_bound_upto
    {D I O S : ℕ → Type*} [∀k,Fintype (D k)] [∀k,Fintype (I k)]
    [∀k,Fintype (O k)] [∀k,Fintype (S k)] [∀k,DecidableEq (S k)]
    [DecidableEq (D 0)]
    (A : ∀k,O k → I k → ℝ) (C : ℕ → ℝ)
    (ei : ∀k,D k ≃ I k×S k) (eo : ∀k,D (k+1) ≃ O k×S k)
    (n : ℕ) (hC : ∀k<n,0≤C k) (hA : ∀k<n,Bound (A k) ((C k)^2))
    (close : D 0 ≃ D n) :
    |∑i,circuit (fun k => wireStep (A k) (ei k) (eo k)) n (close i) i|≤
      (Fintype.card (D 0):ℝ)*(∏k∈Finset.range n,C k) := by
  have hlocal (k : ℕ) (hk : k<n) : Bound (wireStep (A k) (ei k) (eo k)) ((C k)^2) :=
    (hA k hk).wireStep (sq_nonneg _) (ei k) (eo k)
  have hh := (circuit_bound_upto _ (fun k => (C k)^2) n (fun k _ => sq_nonneg _) hlocal).reindex
    close (Equiv.refl (D 0))
  rw [Finset.prod_pow] at hh
  exact hh.trace_abs (Finset.prod_nonneg (fun k hk => hC k (Finset.mem_range.mp hk)))
end LogConcaveSampling.TensorEnergy

end UpperProof
end
end
end

end OAI
