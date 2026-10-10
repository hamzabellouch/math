import OAI.Analysis.OperatorAlgebra.GaussianSchurFactor
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The Gaussian/character integral may be interchanged with an integrable
scalar kernel. This is the actual Fubini step of dual regularization. -/

noncomputable section
open MeasureTheory

namespace WeakPureInfiniteness

theorem gaussian_character_kernel_integral (A : ℝ × ℝ → ℂ)
    (hA : Integrable A (volume.prod volume)) (n : ℕ) :
    (∫ r : ℝ, (realGaussianDensity r : ℂ) *
      ∫ p : ℝ × ℝ, BoundedRecovery.spectralCharacter (-(r / (n + 1 : ℝ)))
        (p.2 - p.1) * A p ∂volume.prod volume) =
      ∫ p : ℝ × ℝ, gaussianSchurFactor n (p.2 - p.1) * A p ∂volume.prod volume := by
  have hρ : Integrable (fun r : ℝ => (realGaussianDensity r : ℂ)) :=
    realGaussianDensity_integrable.ofReal
  have hc : Continuous (fun z : ℝ × (ℝ × ℝ) =>
      BoundedRecovery.spectralCharacter (-(z.1 / (n + 1 : ℝ))) (z.2.2 - z.2.1)) := by
    simp only [BoundedRecovery.spectralCharacter_apply]
    fun_prop
  have hi : Integrable (fun z : ℝ × (ℝ × ℝ) =>
      (realGaussianDensity z.1 : ℂ) *
        (BoundedRecovery.spectralCharacter (-(z.1 / (n + 1 : ℝ))) (z.2.2 - z.2.1) * A z.2))
      (volume.prod (volume.prod volume)) := by
    apply (hρ.mul_prod hA).mono
      (hρ.aestronglyMeasurable.comp_fst.mul
        (hc.aestronglyMeasurable.mul hA.aestronglyMeasurable.comp_snd))
    filter_upwards [] with z
    simp only [Pi.mul_apply, norm_mul, BoundedRecovery.spectralCharacter_norm, one_mul]
    exact le_rfl
  calc
    _ = ∫ r : ℝ, ∫ p : ℝ × ℝ, (realGaussianDensity r : ℂ) *
        (BoundedRecovery.spectralCharacter (-(r / (n + 1 : ℝ))) (p.2 - p.1) * A p)
          ∂volume.prod volume := by simp only [integral_const_mul]
    _ = ∫ p : ℝ × ℝ, (∫ r : ℝ, (realGaussianDensity r : ℂ) *
        (BoundedRecovery.spectralCharacter (-(r / (n + 1 : ℝ))) (p.2 - p.1) * A p))
          ∂volume.prod volume := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      change (∫ r : ℝ, (realGaussianDensity r : ℂ) *
        (BoundedRecovery.spectralCharacter (-(r / (n + 1 : ℝ))) (p.2 - p.1) * A p)) =
          (∫ r : ℝ, (realGaussianDensity r : ℂ) *
            BoundedRecovery.spectralCharacter (-(r / (n + 1 : ℝ))) (p.2 - p.1)) * A p
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with r
      ring

end WeakPureInfiniteness

end

end OAI
