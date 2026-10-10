import Mathlib
import OAI.Geometry.SmoothYau.Geometry.RoundMetricExists

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFlux_C1 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ 1 (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply (hd.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)
  exact (ha.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).mul (hv.clm_apply contDiffAt_const)

omit [FiniteDimensional ℝ E] in
lemma contDiff_realChartLocalize_C2 (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) :
    ContDiff ℝ 2 (realChartLocalize (E := E) p u) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro y hy
  have hyt := tsupport_realChartLocalize_subset (E := E) p u hc hs hy
  rw [contMDiffAt_iff_contDiffAt]
  apply (contDiffAt_inChart_C2 hu p hyt).congr_of_eventuallyEq
  filter_upwards [(chartAt E p).open_target.mem_nhds hyt] with z hz
  exact realChartLocalize_eq p u hz
lemma localGradientPair_change_C2 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v)
    (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localGradientPair g u v q y = localGradientPair g u v p (chartTransition p q y) := by
  let J := coordinateTransitionMatrix p q y
  let du : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  let dv : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (v ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  have hu' : (fun i => fderiv ℝ (u ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ du := by
    ext i
    rw [fderiv_inChart_change_C2 hu p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,du, mul_comm]
  have hv' : (fun i => fderiv ℝ (v ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ dv := by
    ext i
    rw [fderiv_inChart_change_C2 hv p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,dv, mul_comm]
  have hid : J * ((metricCoefficients g q y)⁻¹ * Jᵀ) =
      (metricCoefficients g p (chartTransition p q y))⁻¹ := by
    rw [metricInverse_change_left g p q hy hp, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)),
      Matrix.one_mul]
  unfold localGradientPair
  rw [hu', hv', Matrix.mulVec_mulVec]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hid, dotProduct_comm]

lemma coordinateGradientPair_inChart_C2 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v)
    (g : SmoothMetric E M) (p x : M) (hx : x ∈ (chartAt E p).source) :
    coordinateGradientPair g u v x = localGradientPair g u v p ((chartAt E p) x) := by
  have he := localGradientPair_change_C2 hu hv g p x
    ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  have hbase : coordinateGradientPair g u v x =
      localGradientPair g u v x ((chartAt E x) x) := by
    simp only [coordinateGradientPair, localGradientPair, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hbase, he]
  simp only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)]

lemma contMDiff_coordinateGradientPair_C1 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (coordinateGradientPair g u v) := by
  have hloc (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
      ContDiffAt ℝ 1 (localGradientPair g u v p) y := by
    have hdu := (contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)
    have hdv := (contDiffAt_inChart_C2 hv p hy).fderiv_right (m := 1) (by norm_num)
    unfold localGradientPair dotProduct Matrix.mulVec
    apply ContDiffAt.sum
    intro i _
    apply (hdu.clm_apply contDiffAt_const).mul
    apply ContDiffAt.sum
    intro j _
    have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
    exact (ha.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).mul (hdv.clm_apply contDiffAt_const)
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (hloc x _ hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := coordinateGradientPair_inChart_C2 hu hv g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he
end YauCounterexamples

end

end OAI
