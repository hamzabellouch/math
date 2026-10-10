import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
lemma exists_small_affine_time_tube (a : ℝ) {h τ r η : ℝ}
    (hh : 0 < h) (hτ : 0 < τ) (hr : 0 < r) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η ∧ ε ≤ h ∧
      ∀ s u t : ℝ, |s-a| < ε → |u-a| < ε → |t| < r →
        |s + (u-s)/τ*t-a| < h := by
  let ε := min (h/4) (min η (h*τ/(8*r)))
  have hε : 0 < ε := lt_min (by positivity)
    (lt_min hη (div_pos (mul_pos hh hτ) (by positivity)))
  have hεh : ε ≤ h/4 := min_le_left _ _
  have hεη : ε ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hεr : ε ≤ h*τ/(8*r) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,hεη,by linarith,?_⟩
  intro s u t hs hu ht
  have hus : |u-s| < 2*ε := by
    calc
      |u-s| = |(u-a)+(a-s)| := by congr 1; ring
      _ ≤ |u-a|+|a-s| := abs_add_le _ _
      _ < ε+ε := add_lt_add hu (by simpa only [abs_sub_comm] using hs)
      _ = 2*ε := by ring
  have hm : 2*ε/τ*r ≤ h/4 := by
    have hmul := (le_div_iff₀ (show 0 < 8*r by positivity)).mp hεr
    rw [div_mul_eq_mul_div,div_le_iff₀ hτ]
    nlinarith
  calc
    |s+(u-s)/τ*t-a| = |(s-a)+(u-s)/τ*t| := by congr 1; ring
    _ ≤ |s-a| + |(u-s)/τ*t| := abs_add_le _ _
    _ = |s-a| + |u-s|/τ*|t| := by rw [abs_mul,abs_div,abs_of_pos hτ]
    _ ≤ |s-a| + 2*ε/τ*r := by
      have H := mul_le_mul (div_le_div_of_nonneg_right hus.le hτ.le) ht.le
        (abs_nonneg t) (show 0 ≤ 2*ε/τ by positivity)
      linarith
    _ < ε + 2*ε/τ*r := by linarith
    _ ≤ h/4+h/4 := add_le_add hεh hm
    _ < h := by linarith
end WeakMTWTransport

end

end OAI
