import OAI.Analysis.LipschitzHilbert.Estimates.WeightedOrder

namespace OAI

/-! Finite distributions obtained by observing a size-biased random order. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]

def orderOutcomeWeight (w : ι → ℝ) (s : Finset ι) (X : List ι → α) (a : α) : ℝ :=
  orderAverage w s (fun l => if X l = a then 1 else 0)

omit [Fintype α] in
theorem orderOutcomeWeight_nonnegative (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (X : List ι → α) (a : α) :
    0 ≤ orderOutcomeWeight w s X a := by
  apply orderAverage_nonnegative w s hw
  intro l
  split_ifs <;> norm_num

theorem orderOutcomeWeight_total (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (X : List ι → α) :
    ∑ a, orderOutcomeWeight w s X a = 1 := by
  unfold orderOutcomeWeight
  rw [← orderAverage_sum]
  have heq : (fun l => ∑ a : α, if X l = a then (1 : ℝ) else 0) = fun _ => 1 := by
    funext l
    simp
  rw [heq, orderAverage_const w s hw]

theorem orderOutcomeWeight_event (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (X : List ι → α) (P : α → Prop) [DecidablePred P] :
    (∑ a, if P a then orderOutcomeWeight w s X a else 0) =
      orderAverage w s (fun l => if P (X l) then 1 else 0) := by
  have hpoint (a : α) : (if P a then orderOutcomeWeight w s X a else 0) =
      orderAverage w s (fun l => if P a then if X l = a then 1 else 0 else 0) := by
    by_cases ha : P a
    · simp only [ha, ite_true, orderOutcomeWeight]
    · simp only [ha, ite_false]
      exact (orderAverage_const w s hw 0).symm
  simp_rw [hpoint]
  rw [← orderAverage_sum]
  congr 1
  funext l
  rw [Finset.sum_eq_single (X l)]
  · simp
  · intro a _ ha
    have hxa : X l ≠ a := Ne.symm ha
    simp [hxa]
  · simp

end LipschitzHilbert

end

end OAI
