import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowTimeBlocks
import OAI.Probability.SKBarriers.Locking.NarrowBlockPenalty
import OAI.Probability.SKBarriers.Scalar.NegativePenalty
import OAI.Probability.SKBarriers.Locking.FourBlockTent

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem rawVariance_pos_length {l : List (ℝ × ℝ)} (h : 0<rawVariance l) : 0<l.length := by
  cases l with
  | nil => simp [rawVariance] at h
  | cons p l => simp

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (C : NarrowTimeBlocks α r h q)

theorem v_absCross (hh : 0<h) {θ : ℝ} (hθ : 0≤θ) : weightedAbsCross (C.v θ)=θ := by
  simp only [v,weightedAbsCross_append,weightedAbsCross_zeroWeight,constantWeightChain_absCross,C.j_variance,add_zero]
  rw [abs_of_nonneg (div_nonneg hθ hh.le)]
  field_simp

theorem v_mean_bounds (hα : Monotone α) (hh : 0<h) {θ : ℝ} (hθ : 0≤θ) :
    weightedMean (C.v θ)∈Icc (θ*α r) (θ*α (r+h)) := by
  have HA := rawArea_bounds C.j (C.right.raw_mass_interval hα)
  rw [C.j_variance] at HA
  rw [C.v_mean]
  have hl := mul_le_mul_of_nonneg_left HA.1 (div_nonneg hθ hh.le)
  have hu := mul_le_mul_of_nonneg_left HA.2 (div_nonneg hθ hh.le)
  constructor
  · convert hl using 1; field_simp
  · convert hu using 1; field_simp

theorem scaled_cw (β a : ℝ) :
    scaleIncrementChain β (C.c a)++scaleIncrementChain β (C.w a)=
      fourBlockTent (a/h) (scaleIncrementChain β C.b) (scaleIncrementChain β C.l)
        (scaleIncrementChain β C.j) (scaleIncrementChain β C.k) := by
  simp only [c,w,fourBlockTent,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale,neg_div]

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
