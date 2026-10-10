import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.OpenPlaneBoxes
import OAI.Analysis.RieszRectifiability.Rigidity.HeightTemperedDistribution

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function SchwartzMap

theorem coordinatePlaneMeasure_affine_eq_map {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    coordinatePlaneMeasure (affinePlaneSection a L) =
      Measure.map (fun u : Ambient n => a + L u) volume := by
  change Measure.map ((fun u : Ambient n => a + L u) ∘ WithLp.toLp 2) volume = _
  rw [← (PiLp.volume_preserving_toLp (Fin n)).map_eq,
    Measure.map_map (by fun_prop) (PiLp.volume_preserving_toLp (Fin n)).measurable]

theorem polynomialDecay_affine_pullback_le {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (u : Ambient n) :
    polynomialDecay q u ≤ (1 + ‖a‖) ^ q * polynomialDecay q (a + L u) := by
  have hnorm : 1 + ‖a + L u‖ ≤ (1 + ‖a‖) * (1 + ‖u‖) := by
    have h := norm_add_le a (L u)
    rw [L.norm_map] at h
    nlinarith [norm_nonneg a, norm_nonneg u, mul_nonneg (norm_nonneg a) (norm_nonneg u)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖a + L u‖) hnorm q
  rw [polynomialDecay, polynomialDecay, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖a + L u‖) ^ q)).mpr
  calc
    _ ≤ ((1 + ‖u‖) ^ q)⁻¹ * ((1 + ‖a‖) * (1 + ‖u‖)) ^ q :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

theorem polynomial_weight_integrable_affine_pullback {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (hf : Measurable f)
    (hw : Integrable (fun x => |f x| * polynomialDecay q x)
      (coordinatePlaneMeasure (affinePlaneSection a L))) :
    Integrable (fun u : Ambient n => |f (a + L u)| * polynomialDecay q u) := by
  rw [coordinatePlaneMeasure_affine_eq_map] at hw
  have hI := hw.comp_measurable (show Measurable (fun u : Ambient n => a + L u) by fun_prop)
  apply (hI.const_mul ((1 + ‖a‖) ^ q)).mono'
    (((hf.comp (by fun_prop)).abs.mul (polynomialDecay_measurable q)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro u
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q u))]
  calc
    _ ≤ |f (a + L u)| * ((1 + ‖a‖) ^ q * polynomialDecay q (a + L u)) :=
      mul_le_mul_of_nonneg_left (polynomialDecay_affine_pullback_le q a L u) (abs_nonneg _)
    _ = _ := by ring

theorem exists_intrinsic_height_distribution_from_tail {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : 0 < R)
    (hnear : IntegrableOn f (ball a R) (coordinatePlaneMeasure (affinePlaneSection a L)))
    (hfar : IntegrableOn (fun x => |f x| * inverseDistancePow q a x) (closedExterior a R)
      (coordinatePlaneMeasure (affinePlaneSection a L))) :
    ∃ T : 𝓢'(Ambient n, ℂ), ∀ g : 𝓢(Ambient n, ℂ),
      Integrable (fun u : Ambient n => f (a + L u) • g u) (volume : Measure (Ambient n)) ∧
      T g = ∫ u : Ambient n, f (a + L u) • g u ∂(volume : Measure (Ambient n)) := by
  have hw := polynomial_weight_integrable_from_height_tail q
    (coordinatePlaneMeasure (affinePlaneSection a L)) f hf a R hR hnear hfar
  let F : Ambient n → ℝ := fun u => f (a + L u)
  have hp : Integrable (fun u => |F u| * polynomialDecay q u) (volume : Measure (Ambient n)) :=
    polynomial_weight_integrable_affine_pullback q a L f hf hw
  have hm : Measurable F := hf.comp (show Measurable (fun u : Ambient n => a + L u) by fun_prop)
  refine ⟨heightTemperedDistribution (d := n) (volume : Measure (Ambient n)) F hm q hp, ?_⟩
  intro g
  exact ⟨height_schwartz_integrable (d := n) (volume : Measure (Ambient n)) F hm q hp g,
    heightTemperedDistribution_apply (d := n) (volume : Measure (Ambient n)) F hm q hp g⟩

end

end RieszRectifiability

end OAI
