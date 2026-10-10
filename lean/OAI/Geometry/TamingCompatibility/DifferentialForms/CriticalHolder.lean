import Mathlib

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.CriticalSobolev
open MeasureTheory
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
local instance : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩

lemma schwartz_holder_critical (u φ : 𝓢(E,ℝ)) :
    |∫ x, φ x * u x| ≤ ‖u.toLp 4 (volume : Measure E)‖ *
      ‖φ.toLp (ENNReal.ofReal (4/3:ℝ)) (volume : Measure E)‖ := by
  have hpq : (4:ℝ).HolderConjugate (4/3) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq (u.memLp _ volume) (φ.memLp _ volume)
  rw [SchwartzMap.norm_toLp' (by norm_num : (4:ENNReal) ≠ 0) (by norm_num),
    SchwartzMap.norm_toLp' (by norm_num : ENNReal.ofReal (4/3:ℝ) ≠ 0) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4/3),one_div] at *
  refine le_trans ?_ hh
  have h := norm_integral_le_integral_norm (μ := (volume : Measure E)) (fun x => φ x * u x)
  simpa only [Real.norm_eq_abs,abs_mul,mul_comm] using h

lemma schwartz_multiply_L4 (τ u : 𝓢(E,ℝ)) :
    ‖(SchwartzMap.smulLeftCLM ℝ τ u).toLp 4 (volume : Measure E)‖ ≤
      SchwartzMap.seminorm ℝ 0 0 τ * ‖u.toLp 4 (volume : Measure E)‖ := by
  let T := SchwartzMap.seminorm ℝ 0 0 τ
  have hT : 0 ≤ T := apply_nonneg _ _
  have hb : ∀ᵐ x ∂(volume : Measure E), ‖(SchwartzMap.smulLeftCLM ℝ τ u) x‖ ≤ T * ‖u x‖ := by
    filter_upwards [] with x
    simp only [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,smul_eq_mul]
    change ‖τ x * u x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ τ x) (norm_nonneg _)
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (SchwartzMap.smulLeftCLM ℝ τ u).continuous.aestronglyMeasurable hb 4
  have ht : ENNReal.ofReal T * eLpNorm u 4 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (u.memLp 4 volume).eLpNorm_ne_top
  have h := ENNReal.toReal_mono ht he
  simpa only [SchwartzMap.norm_toLp,ENNReal.toReal_mul,ENNReal.toReal_ofReal hT] using h

lemma schwartz_cutoff_holder_critical (τ u φ : 𝓢(E,ℝ)) :
    |∫ x, φ x * (τ x * u x)| ≤ SchwartzMap.seminorm ℝ 0 0 τ *
      ‖u.toLp 4 (volume : Measure E)‖ * ‖φ.toLp (ENNReal.ofReal (4/3:ℝ)) volume‖ := by
  simpa only [SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,smul_eq_mul] using
    (schwartz_holder_critical (SchwartzMap.smulLeftCLM ℝ τ u) φ).trans
    (mul_le_mul_of_nonneg_right (schwartz_multiply_L4 τ u) (norm_nonneg _))
end TamingCompatibility.CriticalSobolev

end
end

end
end
end

end OAI
