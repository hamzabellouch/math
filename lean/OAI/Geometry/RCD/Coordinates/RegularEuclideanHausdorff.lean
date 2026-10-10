import OAI.Geometry.RCD.Coordinates.MetricLimitHausdorffNormalization
import OAI.Geometry.RCD.Metric.MetricLawCompactness
import OAI.Geometry.RCD.Metric.PointedCompactness
import OAI.Geometry.RCD.Metric.MeasurablePointedApproximation
import OAI.Geometry.RCD.Metric.LowerCurvatureVolume

namespace OAI

/-! # Euclidean measure normalization supplied by an actual regular point -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_euclidean_hausdorff_nonpositive {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {p : X} (hp : IsRegular n p) : hausdorff n (Euclidean n) = volume := by
  let ε := fun k : ℕ => 1/((k:ℝ)+1)
  have he (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have he1 (k : ℕ) : ε k ≤ 1 := by
    dsimp only [ε]
    apply (div_le_one (by positivity)).mpr
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hex (k : ℕ) : ∃ r : ℝ, 0 < r ∧ ∃ V : X → Euclidean n,
      Measurable V ∧ IsPointedApproximation p 0 r 1 (ε k) V ∧ -ε k ≤ K*r^2 := by
    obtain ⟨d,hd,happ⟩ := regular_small_scale_approximation
      (hX.pointedRescalingPrecompactness hn p) hp zero_lt_one (div_pos (he k) (by norm_num : (0:ℝ)<5))
    let r := min (d/2) (min 1 (ε k/(|K|+1)))
    have hr : 0 < r := lt_min (half_pos hd)
      (lt_min zero_lt_one (div_pos (he k) (by positivity)))
    have hrd : r < d := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hd)
    have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hre : r ≤ ε k/(|K|+1) := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨f,hf⟩ := happ r hr hrd
    obtain ⟨V,hVm,hV⟩ := hf.exists_measurable hr zero_lt_one (div_pos (he k) (by norm_num : (0:ℝ)<5))
    have hV' : IsPointedApproximation p 0 r 1 (ε k) V := by
      convert hV using 1
      ring
    refine ⟨r,hr,V,hVm,hV',?_⟩
    have hb := (le_div_iff₀ (by positivity : 0 < |K|+1)).mp hre
    have hs : r^2 ≤ r := by nlinarith only [hr,hr1]
    have hmul := mul_le_mul_of_nonneg_left hs (abs_nonneg K)
    have hlow := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)
    nlinarith only [hb,hmul,hlow,hr]
  choose r hr V hVm hV hcurv using hex
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨Q,α,hα,hlim,_,hpositive⟩ := hX.metric_law_compactness hn zero_lt_one
    (fun _ => p) r ε V hr hε he1
    (fun k => by simpa only [one_mul] using (show (-1:ℝ) ≤ K*(r k)^2 from
      (by linarith only [hcurv k,he1 k]))) hVm hV
  exact hX.metric_limit_hausdorff_normalization hn hK zero_lt_one
    (fun _ => p) (r ∘ α) (ε ∘ α) (V ∘ α) (fun k => hr (α k))
    (hε.comp hα.tendsto_atTop) (fun k => hcurv (α k)) (fun k => hVm (α k))
    (fun k => hV (α k)) (fun _ => (hX.finiteOnBounded _ isBounded_ball).ne) hlim hpositive

theorem NoncollapsedRCD.regular_euclidean_hausdorff {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {p : X} (hp : IsRegular n p) : hausdorff n (Euclidean n) = volume := by
  by_cases hK : K ≤ 0
  · exact hX.regular_euclidean_hausdorff_nonpositive hn hK hp
  · exact (hX.zero_of_nonneg_curvature hn (le_of_not_ge hK)).regular_euclidean_hausdorff_nonpositive
      hn le_rfl hp

end RegularPointCoordinates

end

end OAI
