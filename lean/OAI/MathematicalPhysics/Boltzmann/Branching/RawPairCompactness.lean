import OAI.MathematicalPhysics.Boltzmann.Branching.OuterTightness

namespace OAI

/-! # Compactness bounds for the unweighted collision pair product -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def pairProduct (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  f (z.1,z.2.1)*f (z.1,z.2.2)

theorem pairProduct_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (pairProduct f) := by unfold pairProduct; fun_prop

omit [MeasurableSpace X] in
theorem pairProduct_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : X × (Velocity × Velocity)) : 0 ≤ pairProduct f z := mul_nonneg (hf _) (hf _)

omit [MeasurableSpace X] in
theorem pairProduct_le_pairDensity {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : X × (Velocity × Velocity)) : pairProduct f z ≤ pairDensity f z := by
  have h := mul_le_mul_of_nonneg_right
    (show (1:ℝ) ≤ 1+‖z.2.1‖+‖z.2.2‖ by linarith [norm_nonneg z.2.1,norm_nonneg z.2.2])
    (pairProduct_nonneg hf z)
  unfold pairProduct pairDensity at *
  nlinarith [h]

theorem pairProduct_uniformIntegrable {μ : Measure X} {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hpair : UniformIntegrable (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity)))) :
    UniformIntegrable (fun n => pairProduct (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) :=
  uniformIntegrable_mono_nonneg hpair
    (fun n => (pairProduct_measurable (hfm n)).aestronglyMeasurable)
    (fun n => ae_of_all _ (pairProduct_nonneg (hf n)))
    (fun n => ae_of_all _ (pairProduct_le_pairDensity (hf n)))

theorem pairProduct_unifTight {μ : Measure X} {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hpair : UnifTight (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity)))) :
    UnifTight (fun n => pairProduct (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
  apply Compactness.unifTight_mono hpair
    (fun n => (pairProduct_measurable (hfm n)).aestronglyMeasurable)
  intro n
  filter_upwards [] with z
  rw [Real.enorm_eq_ofReal (pairProduct_nonneg (hf n) z),
    Real.enorm_eq_ofReal (pairDensity_nonneg (hf n) z)]
  exact ENNReal.ofReal_le_ofReal (pairProduct_le_pairDensity (hf n) z)

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
