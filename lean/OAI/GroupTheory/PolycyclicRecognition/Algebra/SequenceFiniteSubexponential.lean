import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # One subexponential radius for a fixed finite family of boxes -/

namespace PolycyclicRecognition

open Filter
open scoped Topology BigOperators

theorem HasSubexponentialUpperBoundSeq.finset_sum {I : Type*}
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop) (s : Finset I)
    (f : I → ℕ → ℝ) (hf : ∀ i ∈ s, HasSubexponentialUpperBoundSeq scale (f i)) :
    HasSubexponentialUpperBoundSeq scale (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sequence_subexponential_upper_const hs 0
  | @insert i s hi ih =>
    have h₁ := hf i (Finset.mem_insert_self _ _)
    have h₂ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h₁.add h₂ hs

theorem finite_subexponential_envelope {I : Type*} [Fintype I]
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    (f : I → ℕ → ℝ) (hf0 : ∀ i n, 0 ≤ f i n)
    (hf : ∀ i, HasSubexponentialUpperBoundSeq scale (f i)) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ i n, f i n ≤ R n := by
  classical
  refine ⟨fun n => ∑ i, f i n, fun n => Finset.sum_nonneg (fun i _ => hf0 i n),
    HasSubexponentialUpperBoundSeq.finset_sum hs Finset.univ f (fun i _ => hf i), ?_⟩
  intro i n
  exact Finset.single_le_sum (fun j _ => hf0 j n) (Finset.mem_univ i)

end PolycyclicRecognition

end OAI
