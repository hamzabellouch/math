import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.MetricSpace.Thickening
import OAI.Geometry.NodalSets.Elliptic.RealWeakConvolution

namespace OAI

namespace Yau
open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution Topology Pointwise
noncomputable section

def realMollifierBump {n : ℕ} (r : ℝ) (hr : 0 < r) (m : ℕ) :
    ContDiffBump (0 : Coord n) :=
  ⟨(r * (1 / ((m:ℝ)+1)))/2, r * (1 / ((m:ℝ)+1)),
    by positivity, by
      have h : 0 < r * (1 / ((m:ℝ)+1)) := by positivity
      linarith⟩

theorem realMollifierBump_radius_tendsto {n : ℕ} (r : ℝ) (hr : 0 < r) :
    Tendsto (fun m ↦ (realMollifierBump (n := n) r hr m).rOut) atTop (𝓝 0) := by
  simpa only [realMollifierBump, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r

theorem realMollifierBump_radius_le {n : ℕ} (r : ℝ) (hr : 0 < r) (m : ℕ) :
    (realMollifierBump (n := n) r hr m).rOut ≤ r := by
  change r*(1/((m:ℝ)+1)) ≤ r
  have h : 1/((m:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  nlinarith

theorem real_convolution_support_in_thickening {n : ℕ} {K : Set (Coord n)}
    (u k : Coord n → ℝ) (r : ℝ) (hu : tsupport u ⊆ K)
    (hk : tsupport k ⊆ closedBall 0 r) :
    tsupport (u ⋆ k) ⊆ cthickening r K := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
  apply mem_cthickening_of_dist_le (a+b) a r K (hu (subset_tsupport u ha))
  have ht := hk (subset_tsupport k hb)
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using ht

theorem real_compact_mollifier_support {n : ℕ} {K L : Set (Coord n)}
    (hK : IsCompact K) (hKL : K ⊆ interior L) :
    ∃ (r : ℝ) (hr : 0 < r), ∀ (u : Coord n → ℝ), tsupport u ⊆ K → ∀ m : ℕ,
      tsupport (u ⋆ (realMollifierBump r hr m).normed volume) ⊆ L := by
  obtain ⟨r,hr,hs⟩ := hK.exists_cthickening_subset_open isOpen_interior hKL
  refine ⟨r,hr,?_⟩
  intro u hu m
  apply (real_convolution_support_in_thickening u _ r hu ?_).trans
    (hs.trans interior_subset)
  rw [(realMollifierBump (n := n) r hr m).tsupport_normed_eq]
  exact closedBall_subset_closedBall (realMollifierBump_radius_le r hr m)

end
end Yau

end OAI
