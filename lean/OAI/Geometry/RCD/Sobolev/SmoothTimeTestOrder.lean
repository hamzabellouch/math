import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Smooth nonnegative time tests control interior interval integrals

Only scalar bumps with one inner and one outer radius are needed. Their
outer radii decrease to the prescribed closed interval.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem integral_closedBall_nonneg_of_smooth_tests
    {a b c r : ℝ} (hr : 0 < r) (ha : a < c-r) (hb : c+r < b)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioo a b))
    (htest : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo a b → (∀ t, 0 ≤ θ t) → 0 ≤ ∫ t in Ioo a b, θ t*f t) :
    0 ≤ ∫ t in closedBall c r, f t := by
  let η := min (c-r-a) (b-c-r)/2
  have hη : 0 < η := by dsimp only [η]; exact half_pos (lt_min (by linarith) (by linarith))
  have hηa : η < c-r-a := by
    have hm := min_le_left (c-r-a) (b-c-r)
    dsimp only [η]
    linarith
  have hηb : η < b-c-r := by
    have hm := min_le_right (c-r-a) (b-c-r)
    dsimp only [η]
    linarith
  let R := fun k : ℕ => r+η*(1/((k:ℝ)+1))
  have hR (k : ℕ) : r < R k := by
    have hp : 0 < η*(1/((k:ℝ)+1)) := mul_pos hη (by positivity)
    dsimp only [R]
    linarith
  have hRle (k : ℕ) : R k ≤ r+η := by
    have hk : 1/((k:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    dsimp only [R]
    exact add_le_add le_rfl (mul_le_of_le_one_right hη.le hk)
  have hRl : Tendsto R atTop (𝓝 r) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η
    simpa only [mul_zero,add_zero] using hh.const_add r
  let χ := fun k : ℕ => (⟨r,R k,hr,hR k⟩ : ContDiffBump c)
  have hsupport (k : ℕ) : tsupport (χ k : ℝ → ℝ) ⊆ Ioo a b := by
    rw [(χ k).tsupport_eq]
    intro t ht
    have hh : |t-c| ≤ R k := by simpa only [mem_closedBall,Real.dist_eq] using ht
    have hh' := abs_le.mp hh
    have hle := hRle k
    exact ⟨by linarith,by linarith⟩
  have hsub : closedBall c r ⊆ Ioo a b := by
    intro t ht
    have hh := abs_le.mp (show |t-c| ≤ r from by simpa only [mem_closedBall,Real.dist_eq] using ht)
    exact ⟨by linarith,by linarith⟩
  have hlimit : Tendsto (fun k => ∫ t in Ioo a b, χ k t*f t) atTop
      (𝓝 (∫ t in Ioo a b, (closedBall c r).indicator f t)) := by
    apply tendsto_integral_of_dominated_convergence (fun t => |f t|)
    · intro k
      exact (χ k).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · exact hf.abs
    · intro k
      exact Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (χ k).nonneg]
        exact mul_le_of_le_one_left (abs_nonneg _) (χ k).le_one
    · exact Eventually.of_forall fun t => by
        by_cases ht : t ∈ closedBall c r
        · have he (k : ℕ) : χ k t = 1 := (χ k).one_of_mem_closedBall ht
          simpa only [he,one_mul,indicator_of_mem ht] using (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => f t) atTop (𝓝 (f t)))
        · have hrt : r < dist t c := lt_of_not_ge (by simpa only [mem_closedBall,dist_comm] using ht)
          have hev := hRl.eventually (gt_mem_nhds hrt)
          apply tendsto_const_nhds.congr'
          filter_upwards [hev] with k hk
          simp only [indicator_of_notMem ht,(χ k).zero_of_le_dist hk.le,zero_mul]
  have he : (∫ t in Ioo a b, (closedBall c r).indicator f t) = ∫ t in closedBall c r, f t := by
    rw [integral_indicator measurableSet_closedBall,Measure.restrict_restrict measurableSet_closedBall,
      inter_eq_left.mpr hsub]
  rw [he] at hlimit
  exact ge_of_tendsto hlimit (Eventually.of_forall fun k =>
    htest (χ k) (χ k).contDiff (χ k).hasCompactSupport (hsupport k) (fun _ => (χ k).nonneg))

end RegularPointCoordinates

end

end OAI
