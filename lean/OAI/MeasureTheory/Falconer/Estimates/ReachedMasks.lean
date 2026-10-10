import OAI.MeasureTheory.Falconer.Angular.SharedAngular
import OAI.MeasureTheory.Falconer.Fourier.DyadicTransforms

namespace OAI

/-!
# Removing reached masks after passing to positive energy

A reached anchor mask is spatially constant on its descendant cell. It
can therefore be taken outside that endpoint transform. Its bounded
angular factor is removed only from the positive independent energy.
-/

namespace Falconer
open Set MeasureTheory

theorem endpointTransform_angular_factor {d : ℕ} (ρ : Measure (Space d))
    (M : ℝ) (b : Space d → Sphere d → ℂ) (m : Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) :
    endpointTransform ρ M (fun x w => m w * b x w) r w =
      m w * endpointTransform ρ M b r w := by
  unfold endpointTransform
  have he : (fun x => Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * (m w * b x w)) =
      fun x => m w * (Complex.exp (Complex.I * (r : ℂ) *
        (inner ℝ (w : Space d) x : ℂ)) * b x w) := by
    funext x
    ring
  rw [he, integral_const_mul, mul_smul_comm]

theorem DyadicCube.endpointTransform_reached_factor {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (M : ℝ) (b m : Space d → Sphere d → ℂ)
    (m₀ : Sphere d → ℂ) (hreached : ∀ x ∈ Q.carrier, ∀ w, m x w = m₀ w)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict Q.carrier) M (fun x w => m x w * b x w) r w =
      m₀ w * endpointTransform (μ.restrict Q.carrier) M b r w := by
  rw [← endpointTransform_angular_factor]
  unfold endpointTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem Q.measurable] with x hx
  rw [hreached x hx w]

theorem sphereMoment_factor_le {d : ℕ} (U : ℝ × Sphere d → ℂ)
    (hU : Measurable U) (m : Sphere d → ℂ) (hm : Measurable m)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmB : ∀ w, ‖m w‖ ≤ B) (hUC : ∀ z, ‖U z‖ ≤ C) (r : ℝ) :
    sphereMoment (fun z => m z.2 * U z) r ≤ B^2 * sphereMoment U r := by
  have hmU : Measurable (fun w => m w * U (r,w)) :=
    hm.mul (hU.comp (measurable_const.prodMk measurable_id))
  have hbound (w : Sphere d) : ‖m w * U (r,w)‖ ≤ B*C := by
    rw [norm_mul]
    exact mul_le_mul (hmB w) (hUC _) (norm_nonneg _) hB
  have hleft := sphere_norm_square_integrable _ hmU (mul_nonneg hB hC) hbound
  have hright := (sphere_norm_square_integrable (fun w => U (r,w))
    (hU.comp (measurable_const.prodMk measurable_id)) hC (fun w => hUC _)).const_mul (B^2)
  change (∫ w, ‖m w * U (r,w)‖^2 ∂sphereMeasure d) ≤
    B^2 * (∫ w, ‖U (r,w)‖^2 ∂sphereMeasure d)
  rw [← integral_const_mul]
  apply integral_mono hleft hright
  intro w
  change ‖m w * U (r,w)‖^2 ≤ B^2 * ‖U (r,w)‖^2
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) hB).mpr (hmB w)) (sq_nonneg _)

/-- Removing two reached angular factors costs only their squared sup
norms. Every unreached spatial mask remains inside its endpoint transform. -/
theorem independentAngularEnergy_remove_factors {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (m n : Sphere d → ℂ) (hm : Measurable m) (hn : Measurable n)
    {B C D E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hmB : ∀ w, ‖m w‖ ≤ B) (hnC : ∀ w, ‖n w‖ ≤ C)
    (hUD : ∀ z, ‖U z‖ ≤ D) (hVE : ∀ z, ‖V z‖ ≤ E) :
    independentAngularEnergy a v Ψ (fun z => m z.2 * U z) (fun z => n z.2 * V z) ≤
      (B^2*C^2) * independentAngularEnergy a v Ψ U V := by
  have hUm : Measurable (fun z : ℝ × Sphere d => m z.2 * U z) :=
    (hm.comp measurable_snd).mul hU
  have hVn : Measurable (fun z : ℝ × Sphere d => n z.2 * V z) :=
    (hn.comp measurable_snd).mul hV
  have hUmB (z : ℝ × Sphere d) : ‖m z.2 * U z‖ ≤ B*D := by
    rw [norm_mul]
    exact mul_le_mul (hmB _) (hUD _) (norm_nonneg _) hB
  have hVnC (z : ℝ × Sphere d) : ‖n z.2 * V z‖ ≤ C*E := by
    rw [norm_mul]
    exact mul_le_mul (hnC _) (hVE _) (norm_nonneg _) hC
  have hi := independentAngularIntegrand_integrable v Ψ _ _ hUm hVn
    (mul_nonneg hB hD) (mul_nonneg hC hE) hUmB hVnC
  have hj := (independentAngularIntegrand_integrable v Ψ U V hU hV hD hE hUD hVE).const_mul
    (B^2*C^2)
  have hpoint (r : ℝ) :
      sphereMoment (fun z => m z.2 * U z) r * sphereMoment (fun z => n z.2 * V z) r ≤
        (B^2*C^2) * (sphereMoment U r * sphereMoment V r) := by
    calc
      _ ≤ (B^2 * sphereMoment U r) * (C^2 * sphereMoment V r) :=
        mul_le_mul (sphereMoment_factor_le U hU m hm hB hD hmB hUD r)
          (sphereMoment_factor_le V hV n hn hC hE hnC hVE r)
          (sphereMoment_nonneg _ _) (mul_nonneg (sq_nonneg _) (sphereMoment_nonneg _ _))
      _ = _ := by ring
  unfold independentAngularEnergy
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a)) *
        ∫ r, (B^2*C^2) * (sphereMoment U r * sphereMoment V r)
          ∂PlanarFalconer.sourceAngularShellMeasure v Ψ :=
      mul_le_mul_of_nonneg_left (integral_mono hi hj hpoint) (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

end Falconer

end OAI
