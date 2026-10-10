import OAI.Probability.InvariantIsing.Fields.FieldGaussianTransformLaw

namespace OAI

/-! Ordinary Gaussian integration preserves radial monotonicity. This is
the exponent-zero endpoint of the backward field comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_gaussian_integral_monotone (v : ℝ≥0) (hv : v ≠ 0)
    (F : ℝ → ℝ) (hF : Measurable F) (hFeven : Function.Even F)
    (hgrowth : HasLinearGrowth F) (hmono : MonotoneOn F (Ici 0)) :
    MonotoneOn (fun z => ∫ u, F u ∂gaussianReal z v) (Ici 0) := by
  let W : ℝ → ℝ → ℝ := fieldFoldedWeight v 0 (fun _ => 0)
  have hw (z : ℝ) : Integrable (fun u : ℝ => Real.exp (0 * (0 : ℝ))) (gaussianReal z v) := by
    simpa only [zero_mul, Real.exp_zero] using (integrable_const (1 : ℝ))
  have hi (z : ℝ) : Integrable (fun u => Real.exp (0 * (0 : ℝ)) * F |u|)
      (gaussianReal z v) := by
    simpa only [zero_mul, Real.exp_zero, one_mul, field_even_abs hFeven] using
      field_gaussian_linear_integrable v z hF hgrowth
  have hW (z : ℝ) : Integrable (W z) (volume.restrict (Ici 0)) :=
    fieldFoldedWeight_integrable v hv z 0 (fun _ => 0) (fun _ => rfl) (hw z)
  have hFW (z : ℝ) : Integrable (fun u => F u * W z u) (volume.restrict (Ici 0)) :=
    field_folded_test_integrable v hv z 0 (fun _ => 0) F (fun _ => rfl) (hi z)
  have hWpos (z : ℝ) : 0 < ∫ u in Ici 0, W z u :=
    fieldFoldedWeight_mass_pos v hv z 0 (fun _ => 0) (fun _ => rfl) (hw z)
  have he (z : ℝ) : (∫ u, F u ∂gaussianReal z v) =
      (∫ u in Ici 0, F u * W z u) / (∫ u in Ici 0, W z u) := by
    simpa [W, field_even_abs hFeven] using
      field_gaussian_folded_ratio v hv z 0 (fun _ => 0) F (fun _ => rfl) (hi z) (hw z)
  intro x hx y _hy hxy
  change (∫ u, F u ∂gaussianReal x v) ≤ ∫ u, F u ∂gaussianReal y v
  rw [he x, he y]
  have hvp : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  exact field_likelihood_ratio_expectation_le (volume.restrict (Ici 0)) (W x) (W y) F
    (ae_restrict_mem measurableSet_Ici) hmono
    (fun u hu w _hw huw => fieldFoldedWeight_parent_order hvp 0 (fun _ => 0) hx hxy hu huw)
    (hW x) (hW y) (hFW x) (hFW y) (hWpos x) (hWpos y)

lemma gaussianOperator_difference_monotone_zero (v : ℝ≥0) (hv : v ≠ 0)
    (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFeven : Function.Even F) (hGeven : Function.Even G)
    (hFgrowth : HasLinearGrowth F) (hGgrowth : HasLinearGrowth G)
    (hFG : MonotoneOn (fun u => G u - F u) (Ici 0)) :
    MonotoneOn (fun z => gaussianOperator 0 v G z - gaussianOperator 0 v F z) (Ici 0) := by
  have hm := field_gaussian_integral_monotone v hv (fun u => G u - F u)
    (hG.sub hF) (fun u => by change G (-u) - F (-u) = G u - F u; rw [hGeven u, hFeven u])
    (field_linearGrowth_sub hFgrowth hGgrowth) hFG
  have he (z : ℝ) : gaussianOperator 0 v G z - gaussianOperator 0 v F z =
      ∫ u, (G u - F u) ∂gaussianReal z v := by
    rw [gaussianOperator_eq_gaussian_integral v hG,
      gaussianOperator_eq_gaussian_integral v hF,
      integral_sub (field_gaussian_linear_integrable v z hG hGgrowth)
        (field_gaussian_linear_integrable v z hF hFgrowth)]
  simpa only [he] using hm

end InvariantIsing

end

end OAI
