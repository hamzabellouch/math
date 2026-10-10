import OAI.Probability.InvariantIsing.Fields.FieldGaussianOrder
import OAI.Probability.InvariantIsing.Fields.CascadeMarking

namespace OAI

/-! Exact one-step Gaussian operator laws used to propagate the radial
comparison through the finite Ising field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_even_abs {F : ℝ → ℝ} (hF : Function.Even F) (u : ℝ) : F |u| = F u := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu, hF u]

lemma field_gaussian_integral_shift (v : ℝ≥0) (z : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) :
    (∫ u, F u ∂gaussianReal z v) = ∫ u, F (z + u) ∂gaussianReal 0 v := by
  have hm : (gaussianReal 0 v).map (fun u => z + u) = gaussianReal z v := by
    simpa only [zero_add] using (gaussianReal_map_const_add (μ := 0) (v := v) z)
  rw [← hm]
  exact integral_map (show AEMeasurable (fun u : ℝ => z + u) (gaussianReal 0 v) from
    (measurable_const.add measurable_id).aemeasurable) hF.aestronglyMeasurable

lemma gaussianOperator_eq_gaussian_integral (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (z : ℝ) :
    gaussianOperator 0 v F z = ∫ u, F u ∂gaussianReal z v := by
  have hm : Measurable (fun u : ℝ => F (z + u)) :=
    hF.comp (measurable_const.add measurable_id)
  rw [field_gaussian_integral_shift v z hF,
    integral_gaussianReal_zero_eq_standard v (F := fun u => F (z + u)) hm]
  simp only [gaussianOperator, ite_true]

lemma gaussianOperator_eq_gaussian_exp_integral {ζ : ℝ} (hζ : ζ ≠ 0)
    (v : ℝ≥0) {F : ℝ → ℝ} (hF : Measurable F) (z : ℝ) :
    gaussianOperator ζ v F z =
      ζ⁻¹ * Real.log (∫ u, Real.exp (ζ * F u) ∂gaussianReal z v) := by
  have hm : Measurable (fun u : ℝ => Real.exp (ζ * F (z + u))) :=
    ((hF.comp (measurable_const.add measurable_id)).const_mul ζ).exp
  rw [field_gaussian_integral_shift v z (hF.const_mul ζ).exp,
    integral_gaussianReal_zero_eq_standard v (F := fun u => Real.exp (ζ * F (z + u))) hm]
  simp only [gaussianOperator, hζ, ite_false]

lemma field_gaussian_integral_reflect (v : ℝ≥0) (z : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F) :
    (∫ u, F u ∂gaussianReal (-z) v) = ∫ u, F u ∂gaussianReal z v := by
  have hm : (gaussianReal z v).map (fun u => -u) = gaussianReal (-z) v :=
    gaussianReal_map_neg

  rw [← hm, integral_map measurable_neg.aemeasurable hF.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall hEven)

lemma gaussianOperator_even (ζ : ℝ) (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F) :
    Function.Even (gaussianOperator ζ v F) := by
  intro z
  by_cases hζ : ζ = 0
  · subst ζ
    rw [gaussianOperator_eq_gaussian_integral v hF,
      gaussianOperator_eq_gaussian_integral v hF,
      field_gaussian_integral_reflect v z hF hEven]
  · rw [gaussianOperator_eq_gaussian_exp_integral hζ v hF,
      gaussianOperator_eq_gaussian_exp_integral hζ v hF,
      field_gaussian_integral_reflect v z (hF.const_mul ζ).exp
        (fun u => by rw [hEven u])]

lemma field_gaussian_linear_integrable (v : ℝ≥0) (z : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (hgrowth : HasLinearGrowth F) :
    Integrable F (gaussianReal z v) := by
  obtain ⟨C, L, _hC, hL, hbound⟩ := hgrowth
  have hi := (integrable_const C).add
    ((gaussianReal_exponentialNormMoments z v 1).const_mul L)
  apply hi.mono' hF.aestronglyMeasurable
  filter_upwards [] with u
  change |F u| ≤ C + L * Real.exp (1 * ‖u‖)
  rw [one_mul]
  exact (hbound u).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp ‖u‖)) hL))

lemma field_linearGrowth_sub {F G : ℝ → ℝ} (hF : HasLinearGrowth F)
    (hG : HasLinearGrowth G) : HasLinearGrowth (fun u => G u - F u) := by
  obtain ⟨CF, LF, hCF, hLF, hF⟩ := hF
  obtain ⟨CG, LG, hCG, hLG, hG⟩ := hG
  refine ⟨CG + CF, LG + LF, add_nonneg hCG hCF, add_nonneg hLG hLF, ?_⟩
  intro u
  calc
    |G u - F u| ≤ |G u| + |F u| := abs_sub _ _
    _ ≤ (CG + LG * ‖u‖) + (CF + LF * ‖u‖) := add_le_add (hG u) (hF u)
    _ = _ := by ring

/-- Gaussian integrability of an even-test tilt supplies integrability of
its folded numerator, also for unbounded linearly growing tests. -/
lemma field_folded_test_integrable (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F f : ℝ → ℝ) (hF : Function.Even F)
    (hf : Integrable (fun u => Real.exp (ζ * F u) * f |u|) (gaussianReal z v)) :
    Integrable (fun u => f u * fieldFoldedWeight v ζ F z u) (volume.restrict (Ici 0)) := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * (Real.exp (ζ * F u) * f |u|)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hf
  have hi : Integrable (fun u => g u + g (-u)) (volume.restrict (Ici 0)) :=
    hg.integrableOn.add hg.comp_neg.integrableOn
  have he : (fun u => g u + g (-u)) =ᵐ[volume.restrict (Ici 0)]
      (fun u => C * (f u * fieldFoldedWeight v ζ F z u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    dsimp only [g]
    rw [abs_of_nonneg hu, abs_neg, abs_of_nonneg hu, hF u]
    have hp := field_gaussian_pair_sum v hv z u
    calc
      _ = (gaussianPDFReal z v u + gaussianPDFReal z v (-u)) *
          (Real.exp (ζ * F u) * f u) := by ring
      _ = _ := by rw [hp]; dsimp only [C, fieldFoldedWeight]; ring
  have hc : C ≠ 0 := (field_folded_constant_pos v hv z).ne'
  have hi' := (hi.congr he).const_mul C⁻¹
  simpa only [Pi.mul_apply, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hi'

end InvariantIsing

end

end OAI
