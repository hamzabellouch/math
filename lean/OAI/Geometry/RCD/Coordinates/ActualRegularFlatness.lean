import OAI.Geometry.RCD.Coordinates.UniformRegularFlatnessInput
import OAI.Geometry.RCD.Coordinates.RegularLimitEuclideanNeighborhood
import OAI.Geometry.RCD.Metric.MovingCompactness
import OAI.Geometry.RCD.Metric.MovingPointedData
import OAI.Geometry.RCD.Metric.InnerIsometryApproximation
import OAI.Geometry.RCD.Metric.LowerCurvatureVolume

namespace OAI

/-! # Uniform pointed flatness in a neighborhood of every regular point

Near-regular compactness and the local metric-limit construction give
Euclidean approximations at every sufficiently small nearby scale.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ}

theorem NoncollapsedRCD.actual_regular_uniform_flatness_nonpositive
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2 ≤ n) (hK : K ≤ 0) {o : X} (ho : IsRegular n o)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : ℝ, 0 < D ∧ ∀ p, dist o p ≤ D → ∀ r : ℝ, 0 < r → r ≤ D/4 →
      ∃ f : X → Euclidean n, IsPointedApproximation p 0 r 2 θ f := by
  classical
  by_contra hnot
  push Not at hnot
  let d := fun k : ℕ => 1/((k:ℝ)+1)
  have hd k : 0 < d k := by dsimp only [d]; positivity
  have hex k := hnot (d k) (hd k)
  choose p hp r hr hrbound hbad using hex
  have hd0 : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hp0 : Tendsto p atTop (𝓝 o) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ hd0
    intro k
    simpa only [dist_comm] using hp k
  have hr0 : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun k => (hr k).le) hrbound (by simpa only [zero_div] using hd0.div_const 4)
  let s := fun k => 256*r k
  have hs k : 0 < s k := mul_pos (by norm_num) (hr k)
  have hs0 : Tendsto s atTop (𝓝 0) := by simpa only [mul_zero] using hr0.const_mul 256
  obtain ⟨φ,hφ,hcurv,Y,dY,hproper,q,hconv⟩ := hX.movingRescalingPrecompactness hn p s hs hs0
  let := dY
  let := hproper
  let : MeasurableSpace Y := borel Y
  let : BorelSpace Y := ⟨rfl⟩
  obtain ⟨α,V,hα,hV⟩ := hconv.subsequence_data (by norm_num : (0:ℝ)<5)
  let ε := fun k : ℕ => 1/((k:ℝ)+1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun k => φ (α k)) atTop atTop := hφ.tendsto_atTop.comp hα.tendsto_atTop
  obtain ⟨f,hf,hfq,hfull⟩ := hX.regular_limit_euclidean_neighborhood hn hK ho
    (fun k => p (φ (α k))) (fun k => s (φ (α k))) ε V
    (hp0.comp ht) (fun k => hs _) (hs0.comp ht) hε (fun k => hcurv _) hV
  have hsmall := hε.eventually (gt_mem_nhds
    (lt_min (by norm_num : (0:ℝ)<1/1024) (div_pos hθ (by norm_num : (0:ℝ)<4096))))
  obtain ⟨k,hk⟩ := hsmall.exists
  have he0 : 0 ≤ ε k := dist_nonneg.trans (hV k).1
  obtain ⟨w,hw⟩ := pointed_approximation_of_inner_isometry (hs _) he0
    (hk.trans_le (min_le_left _ _)) (hV k) f hf hfq hfull
  have hw' : IsPointedApproximation (p (φ (α k))) 0 (r (φ (α k))) 2 (4096*ε k) w := by
    change IsPointedApproximation (p (φ (α k))) 0 (s (φ (α k))/256) 2 (4096*ε k) w at hw
    have he : s (φ (α k))/256 = r (φ (α k)) := by dsimp only [s]; ring
    rwa [he] at hw
  apply hbad (φ (α k)) w
  apply hw'.mono_error
  have hh := hk.trans_le (min_le_right _ _)
  linarith

theorem NoncollapsedRCD.actual_regular_uniform_flatness
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2 ≤ n) {o : X} (ho : IsRegular n o) {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : ℝ, 0 < D ∧ ∀ p, dist o p ≤ D → ∀ r : ℝ, 0 < r → r ≤ D/4 →
      ∃ f : X → Euclidean n, IsPointedApproximation p 0 r 2 θ f := by
  by_cases hK : K ≤ 0
  · exact hX.actual_regular_uniform_flatness_nonpositive hn hK ho hθ
  · exact (hX.zero_of_nonneg_curvature hn (le_of_not_ge hK)).actual_regular_uniform_flatness_nonpositive
      hn le_rfl ho hθ

theorem NoncollapsedRCD.uniformRegularFlatnessInput
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2 ≤ n) : UniformRegularFlatnessInput hX := by
  intro p hp θ hθ
  exact hX.actual_regular_uniform_flatness hn hp hθ

end RegularPointCoordinates

end

end OAI
