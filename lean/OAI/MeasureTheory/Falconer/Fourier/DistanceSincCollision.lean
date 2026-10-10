import OAI.MeasureTheory.Falconer.Fourier.DistanceSincSpectralIdentity

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_collision_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {u A : ℝ} (hA : 0 < A)
    (hu : ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s) :
    ν.real {s : ℝ | |s| ≤ 100/A} ≤ 4 * ∫ s, distanceSincKernel u (A*s) ∂ν := by
  let S : Set ℝ := {s | |s| ≤ 100/A}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hb := integral_mono ((integrable_const (1/4:ℝ)).indicator hS)
    (distanceSincKernel_integrable ν u A) (show ∀ s, S.indicator (fun _ => (1/4:ℝ)) s ≤
      distanceSincKernel u (A*s) from by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs]
        apply hu
        rw [abs_mul,abs_of_pos hA]
        have h := (le_div_iff₀ hA).mp hs
        nlinarith
      · rw [Set.indicator_of_notMem hs]
        exact distanceSincKernel_nonneg _ _)
  rw [integral_indicator_const _ hS,smul_eq_mul] at hb
  dsimp [S] at hb
  linarith

theorem integral_scale_Icc (f : ℝ → ℝ) {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    A * (∫ r in Icc (-u) u, f (A*r)) = ∫ r in Icc (-A*u) (A*u), f r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -u ≤ u),
    ← intervalIntegral.integral_of_le (by nlinarith : -A*u ≤ A*u)]
  have h := intervalIntegral.smul_integral_comp_mul_left f (a := -u) (b := u) A
  simpa only [smul_eq_mul,mul_neg,neg_mul] using h

theorem distanceSincKernel_scaled_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u A : ℝ} (hu : 0 < u) (hu₁ : 2*u ≤ 1) (hA : 0 < A) :
    A*(2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  have h := mul_le_mul_of_nonneg_left (distanceSincKernel_frequency_bound μ hu A) hA.le
  rw [show -2*u = -(2*u) by ring,integral_scale_Icc (fun r => ‖charFun μ r‖^2) hA (by positivity)] at h
  have hs : Icc (-A*(2*u)) (A*(2*u)) ⊆ Icc (-A) A := by
    intro r hr
    constructor <;> nlinarith [hr.1,hr.2]
  have hi : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc (-A) A) := by
    simpa only [one_mul,IntegrableOn] using charFun_sq_integrable_finite μ (volume.restrict (Icc (-A) A)) 1
  have hb := integral_mono_measure (Measure.restrict_mono hs le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ r‖)) hi
  apply le_trans ?_ hb
  simpa only [mul_assoc] using h

theorem finite_measure_distance_collision_fourier : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℝ), 0 < A →
      A * (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} ≤
        C * ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  obtain ⟨u,hu,hu₁,hkernel⟩ := exists_distanceSincKernel
  refine ⟨2/u,by positivity,?_⟩
  intro μ _ A hA
  have hl := distanceSincKernel_collision_bound (distanceDifferenceMeasure μ) hA hkernel
  have hh := distanceSincKernel_scaled_frequency_bound μ hu hu₁ hA
  have he : (distanceDifferenceMeasure μ).real {s : ℝ | |s| ≤ 100/A} =
      (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} := by
    simp only [measureReal_def,distanceDifferenceMeasure]
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    rfl
  rw [he] at hl
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hu).mpr
  have h₁ := mul_le_mul_of_nonneg_left hl (show 0 ≤ A*u by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

end PlanarFalconer

end OAI
