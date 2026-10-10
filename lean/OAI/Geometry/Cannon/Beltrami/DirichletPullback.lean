import Mathlib
import OAI.Geometry.Cannon.Beltrami.TwoPointNormalize

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace CannonBeltrami
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dirichlet_pullback_le (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F : ℂ → ℂ))
    (u : ℂ → E) (hu : ContDiff ℝ 1 u) {S : Set ℂ} (hS : IsCompact S)
    {K : ℝ} (hK : 0 ≤ K)
    (hD : ∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤ K*|(fderiv ℝ (F : ℂ → ℂ) z).det|) :
    (∫ z in S, ‖fderiv ℝ (u ∘ F) z‖^2) ≤
      K*(∫ w in F '' S, ‖fderiv ℝ u w‖^2) := by
  have huD : Continuous (fun z => ‖fderiv ℝ u z‖^2) :=
    (hu.continuous_fderiv (by simp)).norm.pow 2
  have hFi : ∀ z ∈ S, HasFDerivWithinAt (F : ℂ → ℂ) (fderiv ℝ (F : ℂ → ℂ) z) S z :=
    fun z _ => (hF.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hS.measurableSet
    hFi F.injective.injOn (fun z => ‖fderiv ℝ u z‖^2)
  have hint : IntegrableOn (fun z => |(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) S volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS.measurableSet
      hFi F.injective.injOn (fun z => ‖fderiv ℝ u z‖^2)).mp
    exact huD.continuousOn.integrableOn_compact (hS.image F.continuous)
  have hlint : IntegrableOn (fun z => ‖fderiv ℝ (u ∘ F) z‖^2) S volume :=
    ((hu.comp hF).continuous_fderiv (by simp)).norm.pow 2 |>.continuousOn.integrableOn_compact hS
  calc
    _ ≤ ∫ z in S, K*(|(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) := by
      apply setIntegral_mono_on hlint (hint.const_mul K) hS.measurableSet
      intro z _hz
      rw [fderiv_comp z (hu.differentiable (by simp) (F z)) (hF.differentiable (by simp) z)]
      have hn := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ u (F z)) (fderiv ℝ (F : ℂ → ℂ) z)
      have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      have hdistortion := mul_le_mul (hD z) (le_refl (‖fderiv ℝ u (F z)‖^2))
        (sq_nonneg _) (mul_nonneg hK (abs_nonneg _))
      nlinarith [hdistortion]
    _ = K*(∫ z in S, |(fderiv ℝ (F : ℂ → ℂ) z).det| *‖fderiv ℝ u (F z)‖^2) := integral_const_mul _ _
    _ = _ := by rw [hchange]; rfl

theorem beltrami_dirichlet_pullback (F : ℂ ≃ₜ ℂ) (hF : ContDiff ℝ 1 (F : ℂ → ℂ))
    (a b : ℂ → ℂ) (he : ∀ z v, fderiv ℝ (F : ℂ → ℂ) z v=a z*v+b z*star v)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖b z‖ ≤ k*‖a z‖)
    (u : ℂ → E) (hu : ContDiff ℝ 1 u) {S : Set ℂ} (hS : IsCompact S) :
    (∫ z in S, ‖fderiv ℝ (u ∘ F) z‖^2) ≤
      ((1+k)/(1-k))*(∫ w in F '' S, ‖fderiv ℝ u w‖^2) :=
  dirichlet_pullback_le F hF u hu hS (div_nonneg (by linarith) (by linarith))
    (fun z => (wirtinger_energy_distortion (fderiv ℝ (F : ℂ → ℂ) z) (a z) (b z) (he z) hk hk1 (hb z)).2)

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
