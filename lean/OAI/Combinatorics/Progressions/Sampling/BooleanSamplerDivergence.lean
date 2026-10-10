import OAI.Combinatorics.Progressions.Dynamics.BudgetedOpenImageComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem boolean_sampler_divergence_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (hblock : Function.Injective block)
    {h : ℕ} (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    {C R κ : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R) (hc : ∀ o, |c (block o)| ≤ C) (hκ : 0 < κ)
    (w : (BlockParameter B (Fin h) α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hbox : ∀ a ∈ tsupport w, ∀ j, |a j| ≤ R)
    (hdet : ∀ a ∈ tsupport w,
      κ ≤ |((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det|) (i : O) :
    let K := productMinorInverseBound (Fintype.card O) (Fintype.card α) h C R κ
    let H := productMinorDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h C R
    (∫ a, |coordinateDivergence
      (fun j a => w a * selectedInverseField (booleanSamplerMap c sets)
        (booleanSelectedInjection block v r) i j a) a|) ≤
      K * (∑ j, ∫ a, |fderiv ℝ w a (Pi.single j 1)|) +
        (Fintype.card (BlockParameter B (Fin h) α) : ℝ) * (K ^ 2 * H) * ∫ a, |w a| := by
  let U := booleanSamplerMap (F := Fin h) c sets
  let J := booleanSelectedInjection block v r
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let K : ℝ≥0 := ⟨productMinorInverseBound (Fintype.card O) (Fintype.card α) h C R κ,
    productMinorInverseBound_nonneg _ _ _ hC hR0 hκ.le⟩
  let H : ℝ≥0 := ⟨productMinorDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h C R,
    productMinorDerivativeBound_nonneg _ _ _ _ hC hR0⟩
  have hU : ContDiff ℝ 2 U := (booleanSamplerMap_contDiff c sets).of_le (by norm_num)
  have hinfo (a) (ha : a ∈ tsupport w) :
      (selectedDerivative U J a).IsInvertible ∧ ‖(selectedDerivative U J a).inverse‖ ≤ K :=
    boolean_selected_inverse_bound c sets block v r hcard a hC hR0 hc (hbox a ha) hκ (hdet a ha)
  have hder (a) (ha : a ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) a‖ ≤ H :=
    boolean_selected_derivative_bound c sets block v r hcard a hC hR hc (hbox a ha)
  have hbase := selected_inverse_divergence_bound U J w hw hs
    (fun _ _ => hU.contDiffAt) (fun a ha => (hinfo a ha).1) K H
    (fun a ha => (hinfo a ha).2) hder i
  have hJ : ‖J‖ ≤ 1 := booleanSelectedInjection_norm_le block hblock v r
  have hS : 0 ≤ ∑ j, ∫ a, |fderiv ℝ w a (Pi.single j 1)| :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
  have hW : 0 ≤ ∫ a, |w a| := integral_nonneg (fun _ => abs_nonneg _)
  apply hbase.trans
  change (‖J‖ * (K : ℝ)) * _ +
      (Fintype.card (BlockParameter B (Fin h) α) : ℝ) * (‖J‖ * (K : ℝ) ^ 2 * H) * _ ≤
    (K : ℝ) * _ + (Fintype.card (BlockParameter B (Fin h) α) : ℝ) * ((K : ℝ) ^ 2 * H) * _
  have hJK : ‖J‖ * (K : ℝ) ≤ K := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ K.coe_nonneg
  have hJKH : ‖J‖ * (K : ℝ) ^ 2 * H ≤ (K : ℝ) ^ 2 * H := by
    have h := mul_le_mul_of_nonneg_right hJ (sq_nonneg (K : ℝ))
    rw [one_mul] at h
    exact mul_le_mul_of_nonneg_right h H.coe_nonneg
  exact add_le_add (mul_le_mul_of_nonneg_right hJK hS)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJKH (Nat.cast_nonneg _)) hW)

end Erdos3

end

end OAI
