import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientBudget

namespace OAI

/-! Small scalar projections are preserved through each finite
additive/multiplicative closure stage with the explicit saved budget. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_closure_projections {δ K : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (X S : Finset ℝ) (hX : X.Nonempty) (M : ℕ)
    (hS : ∀ a ∈ S, |a| ≤ M)
    (hdoubling : ((scalarCells δ (X+X)).card : ℝ) ≤ K*(scalarCells δ X).card)
    (hproj : ∀ a ∈ S,
      ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤ K*(scalarCells δ X).card)
    (n : ℕ) :
    ∀ a ∈ scalarCoefficientClosure S n,
      ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤
        scalarCoefficientBudget M K n*(scalarCells δ X).card := by
  induction n with
  | zero => exact hproj
  | succ n ih =>
    intro a ha
    let L := scalarCoefficientBudget M K n
    let r := scalarCoefficientRadius M n
    have hL : 1 ≤ L := scalarCoefficientBudget_one_le M hK n
    have hD : ((scalarCells δ (X+X)).card : ℝ) ≤ L*(scalarCells δ X).card :=
      hdoubling.trans (mul_le_mul_of_nonneg_right (scalarCoefficientBudget_zero_le M hK n)
        (Nat.cast_nonneg _))
    have hstep := scalar_coefficient_step_bounds r hL
    change a ∈ (scalarCoefficientClosure S n ∪ -scalarCoefficientClosure S n) ∪
      ((scalarCoefficientClosure S n+scalarCoefficientClosure S n) ∪
        (scalarCoefficientClosure S n*scalarCoefficientClosure S n)) at ha
    change ((scalarCells δ (X+X.image (fun x => a*x))).card : ℝ) ≤
      (32768*((r : ℝ)+4)*L^8)*(scalarCells δ X).card
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · exact (ih a ha).trans (mul_le_mul_of_nonneg_right hstep.1 (Nat.cast_nonneg _))
      · obtain ⟨b,hb,rfl⟩ := Finset.mem_neg.mp ha
        exact (scalar_coefficient_neg δ b (zero_le_one.trans hL) X hX hD (ih b hb)).trans
          (mul_le_mul_of_nonneg_right hstep.2.2.2 (Nat.cast_nonneg _))
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_add.mp ha
        exact (scalar_coefficient_add hδ (zero_le_one.trans hL) X hX hD (ih b hb) (ih c hc)).trans
          (mul_le_mul_of_nonneg_right hstep.2.1 (Nat.cast_nonneg _))
      · obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_mul.mp ha
        exact (scalar_coefficient_mul hδ (zero_le_one.trans hL) X hX r
          (scalarCoefficientClosure_bound S M hS n b hb) hD (ih b hb) (ih c hc)).trans
          (mul_le_mul_of_nonneg_right hstep.2.2.1 (Nat.cast_nonneg _))

end Falconer

end OAI
