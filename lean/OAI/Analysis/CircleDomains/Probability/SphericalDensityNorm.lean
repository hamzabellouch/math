import OAI.Analysis.CircleDomains.Modulus.SphericalWeightedLength

namespace OAI

/-! A quantitative global norm bound for the decaying chart density. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem global_spherical_weighted_density_eLpNorm_le
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    eLpNorm (fun z : ℂ => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)) 2 volume ≤
      (∫⁻x, g x ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  let F : ℂ → ℝ := fun z => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)
  let k : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
  have hF := global_spherical_weighted_density_memLp g hg he
  have hnorm (z : ℂ) : ‖F z‖ₑ ≤ k z := by
    calc
      _ = ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * ENNReal.ofReal (g (z : Sphere)).toReal := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by dsimp [F]; positivity),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 + ‖z‖ ^ 2))]
        congr 1
        dsimp [F]
        ring
      _ ≤ _ := mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc
    _ ≤ ∫⁻z : ℂ, k z ^ 2 := lintegral_mono fun z => pow_le_pow_left' (hnorm z) 2
    _ ≤ ∫⁻x, g x ^ 2 ∂sphericalArea := by
      rw [lintegral_sphericalArea _ (hg.pow_const 2)]
      apply lintegral_mono
      intro z
      dsimp [k]
      rw [mul_pow, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 / (1 + ‖z‖ ^ 2))]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (spherical_weight_sq_le_areaDensity z)) le_rfl

end CircleDomainRigidity

end

end OAI
