import OAI.MeasureTheory.Falconer.Geometry.ProjectionLaw

namespace OAI

/-! # Scalar sinc comparison on the required all-dimensional projection -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projection_collision_band : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure (Space d)) [IsFiniteMeasure μ] (w : Space d) (A H : ℝ),
      0 < A → 0 ≤ H → A ≤ 2*Real.pi*H →
      A*(projectionCollision μ w (100/A)).toReal ≤
        C*(2*Real.pi)*(∫ r in Icc (-H) H, ‖PlanarFalconer.sourceFourier μ (r • w)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := projection_collision_fourier (d := d)
  refine ⟨C,hC,?_⟩
  intro μ _ w A H hA hH hAH
  have hi : IntegrableOn (fun r => ‖charFun (scalarProjectionLaw μ w) r‖^2)
      (Icc (-(2*Real.pi*H)) (2*Real.pi*H)) := by
    simpa only [one_mul,IntegrableOn] using PlanarFalconer.charFun_sq_integrable_finite
      (scalarProjectionLaw μ w) (volume.restrict (Icc (-(2*Real.pi*H)) (2*Real.pi*H))) 1
  have hsub : Icc (-A) A ⊆ Icc (-(2*Real.pi*H)) (2*Real.pi*H) := by
    intro r hr
    constructor <;> linarith [hr.1,hr.2]
  have hmono := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun (scalarProjectionLaw μ w) r‖)) hi
  have hscale := PlanarFalconer.integral_scale_Icc
    (fun r => ‖charFun (scalarProjectionLaw μ w) r‖^2)
    (A := 2*Real.pi) (u := H) (by positivity) hH
  simp_rw [norm_charFun_scalarProjectionLaw] at hscale
  have he : -(2*Real.pi)*H = -(2*Real.pi*H) := by ring
  rw [he] at hscale
  calc
    _ ≤ C*(∫ r in Icc (-A) A, ‖charFun (scalarProjectionLaw μ w) r‖^2) := hbound μ w A hA
    _ ≤ C*(∫ r in Icc (-(2*Real.pi*H)) (2*Real.pi*H),
        ‖charFun (scalarProjectionLaw μ w) r‖^2) := mul_le_mul_of_nonneg_left hmono hC.le
    _ = _ := by rw [← hscale]; ring

end Falconer

end OAI
