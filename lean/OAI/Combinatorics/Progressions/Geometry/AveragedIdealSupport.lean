import OAI.Combinatorics.Progressions.Estimates.ActiveAveragedProfileComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem regularizedAffineIdealDensity_support {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → C d) (c w : ∀ d, C d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) (hδ : 0 < δ)
    (r : ∀ d, C d → ℝ) (hr : ∀ d j, |r d j| ≤ 1)
    {Csum Wsum Ro : ℝ} (hRo : 0 ≤ Ro)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, (|c d j|+|w d j|)) ≤ Wsum)
    (hbound : ∀ d o, Wsum+(2 : ℝ)^(sets d o).card*(Csum*((Fintype.card α : ℝ)+1)^h d) ≤ Ro) :
    ∀ v, Ro+δ < ‖v‖ → regularizedAffineIdealDensity h e index c w sets δ r v = 0 := by
  apply regularizedImageDensity_support (jointBooleanSource h) _ δ hδ hRo
  filter_upwards [jointBooleanSource_ae_closedBall B h] with x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  apply (pi_norm_le_iff_of_nonneg hRo).mpr
  intro o
  have hc : |(monomialArrayPolynomial (e o.1) (fun j => c o.1 j+w o.1 j*r o.1 j)).coeff 0| ≤ Wsum :=
    (monomialArrayPolynomial_coeff_abs_le _ _ 0).trans
      ((Finset.sum_le_sum (fun j _ => affineParameter_abs_upper _ _ _ (hr o.1 j))).trans (hwsum o.1))
  have hb : |booleanConstantJet sets
      (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r d j)).coeff 0) o| ≤ Wsum := by
    unfold booleanConstantJet
    split_ifs
    · exact hc
    · simpa only [abs_zero] using (abs_nonneg _).trans hc
  have hs := jointBooleanSampler_coordinate_abs_le h
    (fun d b => c d (index d b)+w d (index d b)*r d (index d b)) sets x hx o
  have hsum := (affinePrincipal_sum_le (index o.1) (c o.1) (w o.1) (r o.1) (hr o.1)).trans (hcsum o.1)
  have hp : 0 ≤ ((Fintype.card α : ℝ)+1)^h o.1 := by positivity
  have hs' := hs.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hp) (by positivity))
  rw [Real.norm_eq_abs]
  exact (abs_add_le _ _).trans ((add_le_add hb hs').trans (hbound o.1 o.2))

theorem averagedRegularizedIdeal_support {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (e : ∀ d, J d ⊕ N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d) (c w : ∀ d, J d ⊕ N d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) (hδ : 0 < δ)
    {Csum Wsum Ro : ℝ} (hRo : 0 ≤ Ro)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, (|c d j|+|w d j|)) ≤ Wsum)
    (hbound : ∀ d o, Wsum+(2 : ℝ)^(sets d o).card*(Csum*((Fintype.card α : ℝ)+1)^h d) ≤ Ro) :
    ∀ v, Ro+δ < ‖v‖ → averagedRegularizedIdeal h e index c w sets δ v = 0 := by
  intro v hv
  apply integral_eq_zero_of_ae
  filter_upwards [jointUnitCoefficientSource_abs_le J N] with r hr
  exact regularizedAffineIdealDensity_support h e index c w sets δ hδ r hr hRo hcsum hwsum hbound v hv

end Erdos3

end

end OAI
