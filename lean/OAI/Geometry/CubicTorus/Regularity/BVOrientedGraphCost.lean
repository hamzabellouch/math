import Mathlib
import OAI.Geometry.CubicTorus.Reflection.BVTorusGraphFlux

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma norm_sub_inner_normalized_le (v w : Cover) (hw : 1 ≤ ‖w‖) :
    ‖v‖ - ⟪v, ‖w‖⁻¹ • w⟫ ≤ ‖v-w‖^2/2 := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw
  have hsq := norm_sub_sq_real v w
  have hquadratic : ‖v‖-⟪v, ‖w‖⁻¹ • w⟫ ≤ ‖v-w‖^2/(2*‖w‖) := by
    rw [le_div_iff₀ (by positivity : 0 < 2*‖w‖), inner_smul_right]
    have he : (‖v‖-‖w‖⁻¹*⟪v,w⟫)*(2*‖w‖) = 2*‖v‖*‖w‖-2*⟪v,w⟫ := by
      field_simp
    rw [he]
    nlinarith [sq_nonneg (‖v‖-‖w‖)]
  apply hquadratic.trans
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)

def graphSlopeNormal (n : Cover) (p : Plane) : Cover :=
  ‖n-normalPlaneEmbedding n p‖⁻¹ • (n-normalPlaneEmbedding n p)

lemma graphSlopeVector_norm_sq {n : Cover} (hn : ‖n‖ = 1) (p : Plane) :
    ‖n-normalPlaneEmbedding n p‖^2 = 1+‖p‖^2 := by
  rw [norm_sub_sq_real, hn, normalPlaneEmbedding_norm, normalPlaneEmbedding_inner hn]
  ring

lemma graphSlopeVector_norm_ge {n : Cover} (hn : ‖n‖ = 1) (p : Plane) :
    1 ≤ ‖n-normalPlaneEmbedding n p‖ := by
  have hh := graphSlopeVector_norm_sq hn p
  nlinarith [norm_nonneg (n-normalPlaneEmbedding n p), sq_nonneg ‖p‖]

lemma graphSlopeNormal_unit {n : Cover} (hn : ‖n‖ = 1) (p : Plane) :
    ‖graphSlopeNormal n p‖ = 1 := by
  rw [graphSlopeNormal, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) (graphSlopeVector_norm_ge hn p))

def graphOrientedCost (n ν : Cover) (g : Plane → ℝ) (y : Plane) : ℝ :=
  ‖graphAreaVector n g y‖-⟪graphAreaVector n g y,ν⟫

lemma graphOrientedCost_nonneg (n : Cover) {ν : Cover} (hν : ‖ν‖ ≤ 1)
    (g : Plane → ℝ) (y : Plane) : 0 ≤ graphOrientedCost n ν g y := by
  exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hν))

lemma graphOrientedCost_continuous (n ν : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (graphOrientedCost n ν g) :=
  (graphAreaVector_continuous n hg).norm.sub ((graphAreaVector_continuous n hg).inner continuous_const)

lemma graphOrientedCost_slope_le {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (p y : Plane) :
    graphOrientedCost n (graphSlopeNormal n p) g y ≤ ‖gradient g y-p‖^2/2 := by
  have hh := norm_sub_inner_normalized_le (graphAreaVector n g y)
    (n-normalPlaneEmbedding n p) (graphSlopeVector_norm_ge hn p)
  have he : graphAreaVector n g y-(n-normalPlaneEmbedding n p) =
      normalPlaneEmbedding n (p-gradient g y) := by
    simp only [graphAreaVector]
    change n-(normalPlaneLinearIsometry n) (gradient g y)-(n-(normalPlaneLinearIsometry n) p) = (normalPlaneLinearIsometry n) (p-gradient g y)
    rw [map_sub]
    abel
  rw [he, normalPlaneEmbedding_norm, norm_sub_rev p] at hh
  exact hh

lemma graphOrientedCost_trace_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (ν : Cover) {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {w : Cover → ℝ} (hw : Continuous w) (hs : HasCompactSupport w) :
    Integrable (fun y ↦ w (a+normalGraph n g y)*graphOrientedCost n ν g y) := by
  exact ((graph_trace_continuous a n hg.continuous hw).mul
    (graphOrientedCost_continuous n ν hg)).integrable_of_hasCompactSupport
      (graph_trace_compactSupport a hn hg.continuous hs).mul_right

lemma integral_graphSublevel_relative_flux_le (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hs : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (ν : Cover)
    {X : Cover → Cover} (hX : AdmissibleField X) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence (fun y ↦ w y • X y) x) ≤
      (∫ y : Plane, w (a+normalGraph n g y)*graphOrientedCost n ν g y) +
      ∫ x : Cover, graphSublevelIndicator a n g x * divergence (fun y ↦ w y • ν) x := by
  rw [integral_graphSublevel_divergence a hn hg (F := fun y => w y • X y) (hw.smul hX.1) hs.smul_right,
    integral_graphSublevel_divergence a hn hg (F := fun y => w y • ν) (hw.smul_const ν) hs.smul_right]
  have hi := graphOrientedCost_trace_integrable a hn ν hg hw.continuous hs
  have hj := graph_trace_flux_integrable a hn hg (F := fun y => w y • ν) (hw.continuous.smul (continuous_const (y := ν))) hs.smul_right
  rw [← integral_add hi hj]
  apply integral_mono (graph_trace_flux_integrable a hn hg (F := fun y => w y • X y) (hw.continuous.smul hX.1.continuous) hs.smul_right)
    (hi.add hj)
  intro y
  simp only [Pi.add_apply, inner_smul_right, graphOrientedCost]
  have hh : ⟪graphAreaVector n g y,X (a+normalGraph n g y)⟫ ≤ ‖graphAreaVector n g y‖ :=
    (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hX.2.2 _))
  nlinarith [mul_le_mul_of_nonneg_left hh (hw0 (a+normalGraph n g y))]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma normal_constant_admissible {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    AdmissibleField (fun _ : Cover ↦ ν) :=
  ⟨contDiff_const, fun _ _ ↦ rfl, fun _ ↦ hν⟩

lemma cutoff_constant_flux_sub_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    (∫ x in fundamentalCube, characteristic F (quotientMap x) *
      divergence (fun y ↦ w y • ν) x) ≤
    (∫ x in fundamentalCube, characteristic E (quotientMap x) *
      divergence (fun y ↦ w y • ν) x) +
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
  have hdiv (x : Cover) : divergence (fun y ↦ w y • ν) x = ⟪gradient w x,ν⟫ := by
    rw [divergence_smul_function (hw.differentiable (by simp)).differentiableAt
      (differentiableAt_const ν)]
    simp [divergence]
  simp_rw [hdiv]
  have hi : IntegrableOn (fun x ↦ ⟪gradient w x,ν⟫) fundamentalCube :=
    integrableOn_periodic_continuous ((gradient_contDiff hw).continuous.inner continuous_const)
      (fun n x ↦ by rw [gradient_periodic hp])
  have hgn : IntegrableOn (fun x ↦ ‖gradient w x‖) fundamentalCube :=
    integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])
  have ha := integrableOn_characteristic_mul hF.nullMeasurableSet hi
  have hb := integrableOn_characteristic_mul hE.nullMeasurableSet hi
  rw [← sub_le_iff_le_add', ← integral_sub ha hb,
    ← lift_indicator_integral (hE.symmDiff hF).nullMeasurableSet]
  simp_rw [← characteristic_mul]
  apply integral_mono (ha.sub hb)
    (integrableOn_characteristic_mul (hE.symmDiff hF).nullMeasurableSet hgn)
  intro x
  simp only [Pi.sub_apply]
  rw [← sub_mul]
  calc
    _ ≤ |(characteristic F (quotientMap x)-characteristic E (quotientMap x))*⟪gradient w x,ν⟫| := le_abs_self _
    _ = characteristic (E ∆ F) (quotientMap x)*|⟪gradient w x,ν⟫| := by
      rw [abs_mul, characteristic_symmDiff_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hν))
      (characteristic_nonneg _ _)

lemma cutoff_constant_flux_normal {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x+latticeVector n) = w x)
    {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    (∫ x in fundamentalCube, characteristic E (quotientMap x)*divergence (fun y ↦ w y • ν) x) =
      ∫ z : NormalBundle, w z.1 * ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle) := by
  simp_rw [characteristic_mul]
  rw [lift_indicator_integral hE.nullMeasurableSet,
    ← normalMeasure_weighted_flux hμ hw hp (normal_constant_admissible hν)]
  rfl

lemma normalMeasure_sublevelCutoff_inner_tendsto (μ : FiniteMeasure NormalBundle)
    {q : Cover → ℝ} (hq : Continuous q) (hp : ∀ n x, q (x+latticeVector n) = q x)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε atTop (𝓝 0))
    (t : ℝ) {ν : Cover} (hν : ‖ν‖ ≤ 1) :
    Tendsto (fun i ↦ ∫ z : NormalBundle, sublevelCutoff q t (ε i) z.1 * ⟪(z.2 : Cover),ν⟫
      ∂(μ : Measure NormalBundle)) atTop
      (𝓝 (∫ z : NormalBundle in {z | q z.1 < t}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle))) := by
  let A : Set NormalBundle := {z | q z.1 < t}
  have hm : MeasurableSet A := isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  have hh := tendsto_integral_of_dominated_convergence
    (μ := (μ : Measure NormalBundle)) (bound := fun _ ↦ (1 : ℝ))
    (F := fun i z ↦ sublevelCutoff q t (ε i) z.1 * ⟪(z.2 : Cover),ν⟫)
    (f := A.indicator (fun z ↦ ⟪(z.2 : Cover),ν⟫))
    (fun i ↦ (show Continuous (fun z : NormalBundle ↦ sublevelCutoff q t (ε i) z.1 *
      ⟪(z.2 : Cover),ν⟫) from by unfold sublevelCutoff; fun_prop).aestronglyMeasurable)
    (integrable_const 1) (fun i ↦ Eventually.of_forall fun z ↦ ?_)
    (Eventually.of_forall fun z ↦ ?_)
  · simpa only [integral_indicator hm] using hh
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sublevelCutoff_mem_Icc q t (ε i) z.1).1]
    have hz : ‖(z.2 : Cover)‖ = 1 := z.2.property
    have hh : ‖⟪(z.2 : Cover),ν⟫‖ ≤ 1 := by
      exact (norm_inner_le_norm _ _).trans (by simpa only [hz, one_mul] using hν)
    exact (mul_le_mul_of_nonneg_left hh (sublevelCutoff_mem_Icc q t (ε i) z.1).1).trans
      (by simpa only [mul_one] using (sublevelCutoff_mem_Icc q t (ε i) z.1).2)
  · have he : A.indicator (fun z ↦ ⟪(z.2 : Cover),ν⟫) z =
        characteristic (sublevelRegion q t) (quotientMap z.1)*⟪(z.2 : Cover),ν⟫ := by
      classical
      by_cases hz : q z.1 < t <;> simp [A, characteristic, mem_sublevelRegion_quotient hp, hz]
    rw [he]
    exact (sublevelCutoff_tendsto hp hε hεlim t z.1).mul tendsto_const_nhds

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def graphBallOrientedCost (a n ν : Cover) (g : Plane → ℝ) (r : ℝ) : ℝ :=
  ∫ y in {y : Plane | a+normalGraph n g y ∈ Metric.ball a r}, graphOrientedCost n ν g y

lemma graphBallOrientedCost_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ν : Cover} (hν : ‖ν‖ ≤ 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ y : Plane, radialDensityWeight a r (ε i) (a+normalGraph n g y) *
      graphOrientedCost n ν g y) atTop (𝓝 (graphBallOrientedCost a n ν g r)) := by
  have hm : MeasurableSet {y : Plane | a+normalGraph n g y ∈ Metric.ball a r} :=
    Metric.isOpen_ball.measurableSet.preimage (graph_trace_continuous a n hg.continuous
      continuous_id).measurable
  have heps : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hεlim, Eventually.of_forall hε⟩
  have hh := tendsto_integral_of_dominated_convergence
    (bound := fun y : Plane ↦ radialHeightCutoff a r (a+normalGraph n g y) * graphOrientedCost n ν g y)
    (F := fun i y ↦ radialDensityWeight a r (ε i) (a+normalGraph n g y) * graphOrientedCost n ν g y)
    (f := fun y ↦ (Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) (a+normalGraph n g y) *
      graphOrientedCost n ν g y)
    (fun i ↦ (graphOrientedCost_trace_integrable a hn ν hg
      (radialDensityWeight_contDiff a r (ε i)).continuous
      (radialDensityWeight_hasCompactSupport hr.le (hε i))).aestronglyMeasurable)
    (graphOrientedCost_trace_integrable a hn ν hg (radialDensityWeight_contDiff a (2*r) (3*r^2)).continuous
      (radialDensityWeight_hasCompactSupport (by positivity : 0 ≤ 2*r) (by positivity : 0 < 3*r^2)))
    (fun i ↦ Eventually.of_forall fun y ↦ ?_)
    (Eventually.of_forall fun y ↦ ((radialDensityWeight_tendsto a (a+normalGraph n g y) hr).comp heps).mul
      tendsto_const_nhds)
  · convert hh using 1
    rw [graphBallOrientedCost, ← integral_indicator hm]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : a+normalGraph n g y ∈ Metric.ball a r <;>
      simp only [Set.indicator, Set.mem_ofPred_eq, hy, ite_true, ite_false, one_mul, zero_mul]
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (radialDensityWeight_nonneg _ _ _ _)
      (graphOrientedCost_nonneg n hν g y))]
    apply mul_le_mul_of_nonneg_right _ (graphOrientedCost_nonneg n hν g y)
    by_cases hy : a+normalGraph n g y ∈ Metric.closedBall a r
    · rw [radialHeightCutoff_one hr hy]
      exact radialDensityWeight_le_one _ _ _ _
    · have hd : r ≤ ‖(a+normalGraph n g y)-a‖ := le_of_lt (by
        simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hy)
      rw [radialDensityWeight_zero hr.le (hε i) hd]
      exact Real.smoothTransition.nonneg _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def bundleOrientedExcess (μ : FiniteMeasure NormalBundle) (ν : Cover) (r : ℝ) : ℝ :=
  ∫ z : NormalBundle in {z | radialSquared z.1 < r^2}, 1-⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)

lemma bundleOrientedExcess_eq (μ : FiniteMeasure NormalBundle) (ν : Cover) (r : ℝ) :
    bundleOrientedExcess μ ν r = (μ : Measure NormalBundle).real {z | radialSquared z.1 < r^2} -
      ∫ z : NormalBundle in {z | radialSquared z.1 < r^2}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle) := by
  rw [bundleOrientedExcess, integral_sub (integrable_const 1)
    ((show Continuous (fun z : NormalBundle ↦ ⟪(z.2 : Cover),ν⟫) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real_def, Measure.restrict_apply_univ]

theorem isMinimizerAt_oriented_graph_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (n : Cover), ‖n‖ = 1 →
      ∀ (ν : Cover), ‖ν‖ ≤ 1 → ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ r K d : ℝ, 0 < r → r < 1/4 → (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      HasDerivAt (sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared) d (r^2) →
      sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (r^2) < η →
      bundleOrientedExcess μ ν r ≤ graphBallOrientedCost cubeCenter n ν g r +
        2*K*(2*r)*d + C*sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (r^2) := by
  obtain ⟨η,C,hη,hC,hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η,C,hη,hC,?_⟩
  intro n hn ν hν g hg r K d hr hs hK hd ht
  let F := torusGraphRegion cubeCenter n g
  have hF : MeasurableSet F := measurableSet_torusGraphRegion _ _ hg.continuous
  let ε : ℕ → ℝ := fun i ↦ 1/((i : ℝ)+1)
  have he : ∀ i, 0 < ε i := fun i ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let m := sublevelVolume (E ∆ F) radialSquared
  let A : ℕ → ℝ := fun i ↦ ∫ y : Plane, radialDensityWeight cubeCenter r (ε i)
    (cubeCenter+normalGraph n g y)*graphOrientedCost n ν g y
  let N : ℕ → ℝ := fun i ↦ ∫ z : NormalBundle, sublevelCutoff radialSquared (r^2) (ε i) z.1 *
    ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)
  let D : ℕ → ℝ := fun i ↦ K*(2*r)*((m (r^2)-m (r^2-ε i))/ε i)
  let L : ℕ → ℝ := fun i ↦ A i + N i + D i
  have hAlim := graphBallOrientedCost_tendsto cubeCenter hn hν hg hr he helim
  have hNlim := normalMeasure_sublevelCutoff_inner_tendsto μ radialSquared_contDiff.continuous
    radialSquared_periodic he helim (r^2) hν
  have hDlim : Tendsto D atTop (𝓝 (K*(2*r)*d)) :=
    tendsto_const_nhds.mul (tendsto_backward_quotient_of_hasDerivAt hd he helim)
  have hlim : Tendsto L atTop (𝓝 (graphBallOrientedCost cubeCenter n ν g r +
      (∫ z : NormalBundle in {z | radialSquared z.1 < r^2}, ⟪(z.2 : Cover),ν⟫ ∂(μ : Measure NormalBundle)) +
      K*(2*r)*d)) := (hAlim.add hNlim).add hDlim
  have hlocal (i : ℕ) (X : Cover → Cover) (hX : AdmissibleField X) :
      (∫ x in fundamentalCube, characteristic F (quotientMap x) *
        divergence (fun y ↦ sublevelCutoff radialSquared (r^2) (1/((i : ℝ)+1)) y • X y) x) ≤ L i := by
    let w := radialDensityWeight cubeCenter r (ε i)
    have hw : ContDiff ℝ (⊤ : ℕ∞) w := radialDensityWeight_contDiff _ _ _
    have hwc : HasCompactSupport w := radialDensityWeight_hasCompactSupport hr.le (he i)
    have hws : tsupport w ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
      radialDensityWeight_cell_support hr.le (by linarith) (he i)
    have hperiod : latticePeriodize w = sublevelCutoff radialSquared (r^2) (ε i) :=
      radialDensityWeight_periodize hr.le hs (he i)
    have hf := integral_graphSublevel_relative_flux_le cubeCenter hn hg hw hwc
      (fun x ↦ radialDensityWeight_nonneg _ _ _ x) ν hX
    rw [← interior_cutoff_flux_eq cubeCenter n g hwc hws X,
      ← interior_cutoff_flux_eq cubeCenter n g hwc hws (fun _ ↦ ν), hperiod] at hf
    have hdif := cutoff_constant_flux_sub_le hE hF
      (sublevelCutoff_contDiff radialSquared_contDiff (r^2) (ε i))
      (sublevelCutoff_periodic radialSquared_periodic (r^2) (ε i)) hν
    rw [cutoff_constant_flux_normal hE hμ
      (sublevelCutoff_contDiff radialSquared_contDiff (r^2) (ε i))
      (sublevelCutoff_periodic radialSquared_periodic (r^2) (ε i)) hν] at hdif
    have hgrad := sublevelCutoff_gradient_integral_le (hE.symmDiff hF) radialSquared_contDiff
      radialSquared_periodic hK (norm_gradient_radialSquared hr.le hs.le) (he i)
    change _ ≤ A i + _ at hf
    change _ ≤ N i + _ at hdif
    change _ ≤ D i at hgrad
    dsimp only [L]
    linarith
  obtain ⟨hG,hb⟩ := perimeter_glued_local_flux_le hE hF hμ radialSquared_contDiff
    radialSquared_periodic hK (norm_gradient_radialSquared hr.le hs.le) hd hlim hlocal
  have hdist : regionDistance E (gluedRegion E F (sublevelRegion radialSquared (r^2))) =
      sublevelVolume (E ∆ F) radialSquared (r^2) :=
    regionDistance_gluedRegion hE.nullMeasurableSet hF.nullMeasurableSet
      (measurableSet_sublevelRegion radialSquared_contDiff.continuous.measurable _).nullMeasurableSet
  have hcomp := hc _ hG (hdist ▸ ht)
  rw [hdist] at hcomp
  rw [hμ.1] at hb
  rw [bundleOrientedExcess_eq]
  change _ ≤ graphBallOrientedCost cubeCenter n ν g r + 2*K*(2*r)*d +
    C*sublevelVolume (E ∆ F) radialSquared (r^2)
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeGradient_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient g) := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp))

lemma smooth_graph_relative_energy_integrable {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p : Plane) (r : ℝ) :
    IntegrableOn (fun y ↦ ‖gradient g y-p‖^2) (Metric.ball (0 : Plane) r) := by
  apply (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) r)
    ((((planeGradient_contDiff hg).continuous.sub continuous_const).norm).pow 2).continuousOn).mono_set
    Metric.ball_subset_closedBall

lemma graphBallOrientedCost_le_disk (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p : Plane) (r : ℝ) :
    graphBallOrientedCost a n (graphSlopeNormal n p) g r ≤
      (∫ y in Metric.ball (0 : Plane) r, ‖gradient g y-p‖^2)/2 := by
  let S : Set Plane := {y | a+normalGraph n g y ∈ Metric.ball a r}
  have hsub : S ⊆ Metric.ball (0 : Plane) r := by
    intro y hy
    have hh : ‖normalGraph n g y‖ < r := by
      simpa only [S, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hy
    simpa only [Metric.mem_ball, dist_zero_right] using (normalGraph_norm_ge hn g y).trans_lt hh
  have hi := smooth_graph_relative_energy_integrable hg p r
  have hcost : IntegrableOn (graphOrientedCost n (graphSlopeNormal n p) g) (Metric.ball (0 : Plane) r) :=
    ((graphOrientedCost_continuous n _ hg).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) r)).mono_set Metric.ball_subset_closedBall
  calc
    _ ≤ ∫ y in S, ‖gradient g y-p‖^2/2 :=
      integral_mono (hcost.mono_set hsub) (IntegrableOn.mono_set (hi.div_const 2) hsub)
        (graphOrientedCost_slope_le hn g p)
    _ ≤ ∫ y in Metric.ball (0 : Plane) r, ‖gradient g y-p‖^2/2 :=
      setIntegral_mono_set (hi.div_const 2) (Eventually.of_forall fun y ↦ by positivity)
        hsub.eventuallyLE
    _ = _ := by rw [integral_div]

lemma bundleOrientedExcess_nonneg (μ : FiniteMeasure NormalBundle) {ν : Cover}
    (hν : ‖ν‖ ≤ 1) (r : ℝ) : 0 ≤ bundleOrientedExcess μ ν r := by
  apply integral_nonneg
  intro z
  have hz : ‖(z.2 : Cover)‖ = 1 := z.2.property
  exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans (by simpa only [hz, one_mul] using hν))

lemma bundleOrientedExcess_mono (μ : FiniteMeasure NormalBundle) {ν : Cover}
    (hν : ‖ν‖ ≤ 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    bundleOrientedExcess μ ν r ≤ bundleOrientedExcess μ ν s := by
  have hi : Integrable (fun z : NormalBundle ↦ 1-⟪(z.2 : Cover),ν⟫) (μ : Measure NormalBundle) :=
    (show Continuous (fun z : NormalBundle ↦ 1-⟪(z.2 : Cover),ν⟫) from by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply setIntegral_mono_set hi.integrableOn
  · exact Eventually.of_forall fun z ↦ by
      have hz : ‖(z.2 : Cover)‖ = 1 := z.2.property
      exact sub_nonneg.mpr ((real_inner_le_norm _ _).trans (by simpa only [hz, one_mul] using hν))
  · exact (show {z : NormalBundle | radialSquared z.1 < r^2} ⊆ {z | radialSquared z.1 < s^2} from
      fun z hz ↦ hz.trans_le (sq_le_sq₀ hr (hr.trans hrs) |>.mpr hrs)).eventuallyLE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

lemma compact_convolution_gradient_lipschitz {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure] {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : X → ℝ, Integrable f μ → ∀ x y : X,
      let u := f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k
      ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ C*(∫ z, ‖f z‖ ∂μ)*‖x-y‖ := by
  obtain ⟨C,hC,hbound⟩ := smooth_compact_hessian_bound hk hs
  refine ⟨C,hC,fun f hf x y ↦ ?_⟩
  let u := f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hs.contDiff_convolution_right _ hf.locallyIntegrable hk
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) := hu.fderiv_right (by simp)
  exact (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hd.differentiable (by simp) |>.differentiableAt)
    (fun z _ ↦ second_deriv_convolution_le hf hk hs hC.le hbound z)
    (mem_univ y) (mem_univ x)

theorem plane_weak_harmonic_smooth_representative {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Plane → ℝ, Integrable f →
      (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 (4*R) → (∫ y, f y * Δ φ y) = 0) →
      ∃ u : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧
        f =ᵐ[volume.restrict (Metric.ball 0 R)] u ∧
        ∀ x y : Plane, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ C*(∫ z, ‖f z‖)*‖x-y‖ := by
  let L := Complex.orthonormalBasisOneI.repr
  obtain ⟨k,κ,hk,hks,hrad,hc,hκ,_,hi⟩ := exists_radial_smoothing_kernel hR
  obtain ⟨C,hC,hgrad⟩ := compact_convolution_gradient_lipschitz (μ := volume) hk hks
  refine ⟨C,hC,fun f hf hw ↦ ?_⟩
  let v := (f ∘ L) ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  have hfL : Integrable (f ∘ L) := (L.measurePreserving.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hks.contDiff_convolution_right _ hfL.locallyIntegrable hk
  refine ⟨v ∘ L.symm,hv.comp L.symm.contDiff,?_,?_⟩
  · have he := weak_harmonic_radial_reproduction hR (Subset.refl _) hfL.locallyIntegrable
      (weak_harmonic_comp_isometry L hw) hk hks hrad hc hκ hi
    have hmp : MeasurePreserving L.symm
        (volume.restrict (Metric.ball (0 : Plane) R))
        (volume.restrict (Metric.ball (0 : ℂ) R)) := by
      simpa only [L.symm.preimage_ball, map_zero] using
        L.symm.measurePreserving.restrict_preimage (measurableSet_ball (x := (0 : ℂ)) (ε := R))
    have hh := hmp.quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [hh] with z hz
    change f (L (L.symm z)) = v (L.symm z) at hz
    change f z = v (L.symm z)
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hz
  · intro x y
    have he (z : Plane) : fderiv ℝ (v ∘ L.symm) z =
        (fderiv ℝ v (L.symm z)).comp L.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
      rw [fderiv_comp z (hv.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
      congr 1
      exact L.symm.toContinuousLinearEquiv.toContinuousLinearMap.fderiv
    rw [he x, he y, ← ContinuousLinearMap.sub_comp]
    have hh : ‖L.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
      exact L.symm.toLinearIsometry.norm_toContinuousLinearMap_le
    calc
      _ ≤ ‖fderiv ℝ v (L.symm x)-fderiv ℝ v (L.symm y)‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hh)
      _ ≤ C*(∫ z, ‖(f ∘ L) z‖)*‖L.symm x-L.symm y‖ := hgrad _ hfL _ _
      _ = _ := by
        rw [← map_sub, L.symm.norm_map]
        dsimp only [Function.comp_def]
        rw [L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding (fun z ↦ ‖f z‖)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma plane_gradient_oscillation_energy {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hb : ∀ x : Plane, ‖fderiv ℝ u x-fderiv ℝ u 0‖ ≤ A*‖x‖) :
    (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u x-fderiv ℝ u 0‖^2) ≤ Real.pi*A^2*ρ^4 := by
  have hi : IntegrableOn (fun x ↦ ‖fderiv ℝ u x-fderiv ℝ u 0‖^2) (Metric.ball (0 : Plane) ρ) :=
    (((hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) ρ) |>.mono_set Metric.ball_subset_closedBall
  have hpoint : ∀ x ∈ Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u x-fderiv ℝ u 0‖^2 ≤ A^2*ρ^2 := by
    intro x hx
    have hxρ : ‖x‖ ≤ ρ := by simpa only [dist_zero_right] using (show dist x 0 < ρ from hx).le
    calc
      _ ≤ (A*‖x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
      _ ≤ (A*ρ)^2 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫ _ in Metric.ball (0 : Plane) ρ, A^2*ρ^2 := by
      apply integral_mono_ae hi (integrableOn_const measure_ball_lt_top.ne)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hpoint x hx
    _ = _ := by
      rw [integral_const, smul_eq_mul, show (volume.restrict (Metric.ball (0 : Plane) ρ)).real univ =
        volume.real (Metric.ball (0 : Plane) ρ) by simp [Measure.real], plane_ball_real hρ]
      ring

theorem planar_H1_strong_harmonic_approximation {R : ℝ} (hR : 0 < R)
    {K : Set Plane} (hK : IsCompact K) (hball : Metric.ball (0 : Plane) (4*R) ⊆ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
      (∀ i, LipschitzWith (L i) (f i)) →
      (∀ i, Integrable (fun x ↦ f i x^2)) →
      (∀ i, Integrable (fun x ↦ ‖fderiv ℝ (f i) x‖^2)) →
      ∀ M D : ℝ, 0 ≤ D → (∀ i, (∫ x, f i x^2) ≤ M) →
      (∀ i, (∫ x, ‖fderiv ℝ (f i) x‖^2) ≤ D) →
      (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 (4*R) → Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (u : Plane → ℝ), StrictMono ψ ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
        Tendsto (fun i ↦ ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-u x)^2) atTop (𝓝 0) ∧
        ∀ ρ : ℝ, 0 ≤ ρ →
          (∫ x in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ u x-fderiv ℝ u 0‖^2) ≤ C*M*ρ^4 := by
  obtain ⟨C₀,hC₀,hsmooth⟩ := plane_weak_harmonic_smooth_representative hR
  let vK := (volume : Measure Plane).real K
  refine ⟨Real.pi*C₀^2*(vK+1), by dsimp [vK]; positivity, ?_⟩
  intro f L hf hfs hgrad M D hD hM hbound hw
  obtain ⟨u,ψ,hψ,hmem,hu⟩ := restricted_H1_subsequence hK f L hf hfs hgrad hD hM hbound
  have hM0 : 0 ≤ M := (integral_nonneg fun x ↦ sq_nonneg (f 0 x)).trans (hM 0)
  have hnorm : ‖u‖^2 ≤ M := by
    apply le_of_tendsto (hu.norm.pow 2)
    exact Eventually.of_forall fun i ↦ by
      rw [L2_norm_sq_integral]
      calc
        _ = ∫ x in K, f (ψ i) x^2 := integral_congr_ae ((hmem (ψ i)).coeFn_toLp.mono fun x hx ↦ by rw [hx])
        _ ≤ ∫ x, f (ψ i) x^2 := integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun x ↦ sq_nonneg _) (hfs (ψ i))
        _ ≤ M := hM (ψ i)
  let U : Plane → ℝ := K.indicator (fun x ↦ u x)
  have hU := L2_zero_extension_bounds hK.measurableSet hK.measure_lt_top.ne u
  have hweak := L2_weak_harmonic_limit hK hball (fun i ↦ hmem (ψ i)) hu
    (fun φ hφ hs hb ↦ (hw φ hφ hs hb).comp hψ.tendsto_atTop)
  obtain ⟨v,hv,he,hvgrad⟩ := hsmooth U hU.1 hweak
  have hRK : Metric.ball (0 : Plane) R ⊆ K :=
    (Metric.ball_subset_ball (by linarith : R ≤ 4*R)).trans hball
  have hueq : (fun x ↦ u x) =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] v := by
    filter_upwards [he,ae_restrict_mem measurableSet_ball] with x hx hxR
    rw [show U x = u x from indicator_of_mem (hRK hxR) _] at hx
    exact hx
  refine ⟨ψ,v,hψ,hv,?_,?_⟩
  · have hsmall : Tendsto (fun i ↦ ∫ x in K, (f (ψ i) x-u x)^2) atTop (𝓝 0) := by
      have hh := (hu.dist (tendsto_const_nhds (x := u))).pow 2
      simpa only [dist_self, zero_pow (by norm_num : 2 ≠ 0), L2_toLp_dist_sq] using hh
    apply squeeze_zero (fun i ↦ integral_nonneg fun x ↦ sq_nonneg _) (fun i ↦ ?_) hsmall
    calc
      _ = ∫ x in Metric.ball (0 : Plane) R, (f (ψ i) x-u x)^2 :=
        integral_congr_ae (hueq.mono fun x hx ↦ by dsimp only at hx ⊢; rw [hx])
      _ ≤ _ := integral_mono_measure (Measure.restrict_mono hRK le_rfl)
        (Eventually.of_forall fun x ↦ sq_nonneg _)
        ((memLp_two_iff_integrable_sq ((hmem (ψ i)).sub (Lp.memLp u)).aestronglyMeasurable).mp
          ((hmem (ψ i)).sub (Lp.memLp u)))
  · intro ρ hρ
    have hi0 : 0 ≤ ∫ z, ‖U z‖ := integral_nonneg fun z ↦ norm_nonneg _
    have hb : (∫ z, ‖U z‖)^2 ≤ vK*M := hU.2.trans (mul_le_mul_of_nonneg_left hnorm measureReal_nonneg)
    have hh := plane_gradient_oscillation_energy hv (mul_nonneg hC₀.le hi0) hρ
      (fun x ↦ by simpa only [sub_zero] using hvgrad x 0)
    apply hh.trans
    have hnon : 0 ≤ Real.pi*C₀^2*ρ^4 := by positivity
    have hc := mul_le_mul_of_nonneg_left hb hnon
    have hadd : 0 ≤ Real.pi*C₀^2*M*ρ^4 := by positivity
    nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma sublevelVolume_relative_difference {E F G : Set Torus} {q : Cover → ℝ}
    (hq : Measurable q) {s t : ℝ} (hst : s ≤ t)
    (hchange : F ∆ G ⊆ sublevelRegion q s) :
    sublevelVolume (E ∆ G) q t-sublevelVolume (E ∆ F) q t =
      sublevelVolume (E ∆ G) q s-sublevelVolume (E ∆ F) q s := by
  have hsub : sublevelRegion q s ⊆ sublevelRegion q t := fun x hx ↦ lt_of_lt_of_le hx hst
  have hg := measureReal_inter_add_sdiff (μ := torusVolume)
    (s := (E ∆ G) ∩ sublevelRegion q t) (measurableSet_sublevelRegion hq s)
  have hf := measureReal_inter_add_sdiff (μ := torusVolume)
    (s := (E ∆ F) ∩ sublevelRegion q t) (measurableSet_sublevelRegion hq s)
  have hi (A : Set Torus) : (A ∩ sublevelRegion q t) ∩ sublevelRegion q s = A ∩ sublevelRegion q s := by
    ext x
    simp only [mem_inter_iff]
    exact ⟨fun hx ↦ ⟨hx.1.1,hx.2⟩, fun hx ↦ ⟨⟨hx.1,hsub hx.2⟩,hx.2⟩⟩
  have he : ((E ∆ G) ∩ sublevelRegion q t) \ sublevelRegion q s =
      ((E ∆ F) ∩ sublevelRegion q t) \ sublevelRegion q s := by
    ext x
    have hx : x ∉ sublevelRegion q s → (x ∈ F ↔ x ∈ G) := by
      intro hxs
      by_contra hh
      have hm : x ∈ F ∆ G := by
        simp only [Set.mem_symmDiff]
        tauto
      exact hxs (hchange hm)
    simp only [Set.mem_sdiff, mem_inter_iff, Set.mem_symmDiff]
    constructor <;> intro hh
    · have he := hx hh.2
      tauto
    · have he := hx hh.2
      tauto
  rw [hi] at hg hf
  rw [he] at hg
  dsimp only [sublevelVolume]
  linarith

lemma hasDerivAt_sublevelVolume_of_interior_change {E F G : Set Torus} {q : Cover → ℝ}
    (hq : Measurable q) {s t d : ℝ} (hst : s < t)
    (hchange : F ∆ G ⊆ sublevelRegion q s)
    (hd : HasDerivAt (sublevelVolume (E ∆ F) q) d t) :
    HasDerivAt (sublevelVolume (E ∆ G) q) d t := by
  let c := sublevelVolume (E ∆ G) q s-sublevelVolume (E ∆ F) q s
  have he : sublevelVolume (E ∆ G) q =ᶠ[𝓝 t] fun u ↦ sublevelVolume (E ∆ F) q u+c := by
    filter_upwards [eventually_gt_nhds hst] with u hu
    have hh := sublevelVolume_relative_difference (E := E) hq hu.le hchange
    dsimp only [c]
    linarith
  exact (hd.add_const c).congr_of_eventuallyEq he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_oriented_interior_low_slice {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (n : Cover), ‖n‖ = 1 →
      ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ (p : Plane) (F : Set Torus), MeasurableSet F →
      ∀ a b B T K : ℝ, 0 < a → a < b → b < 1/4 → T < η →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      F ∆ torusGraphRegion cubeCenter n g ⊆ sublevelRegion radialSquared (a^2) →
      sublevelVolume (E ∆ F) radialSquared (b^2) < B →
      sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (b^2) < T →
      bundleOrientedExcess μ (graphSlopeNormal n p) a ≤
        (∫ y in Metric.ball (0 : Plane) b, ‖gradient g y-p‖^2)/2 +
          4*K*b*B/(b^2-a^2)+C*T := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_oriented_graph_replacement hV hE hmin hμ
  refine ⟨η,C,hη,hC,?_⟩
  intro n hn g hg p F hF a b B T K ha hab hbs hT hK hchange he htotal
  let m := sublevelVolume (E ∆ F) radialSquared
  have hm : Monotone m := sublevelVolume_mono _ _
  have ha2b2 : a^2 < b^2 := by nlinarith
  have hmb : m (b^2) < B := he
  have hmb0 : 0 ≤ m (b^2) := measureReal_nonneg
  have hB0 : 0 < B := hmb0.trans_lt hmb
  have hden : 0 < b^2-a^2 := sub_pos.mpr ha2b2
  have hbound : m (b^2)-m (a^2) < (B/(b^2-a^2))*(b^2-a^2) := by
    rw [div_mul_cancel₀ _ hden.ne']
    have hh : 0 ≤ m (a^2) := measureReal_nonneg
    linarith
  obtain ⟨t,ht,hd,hder⟩ := monotone_exists_deriv_le hm ha2b2 hbound
  let ρ := Real.sqrt t
  have ht0 : 0 < t := (sq_nonneg a).trans_lt ht.1
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
  have hρsq : ρ^2 = t := Real.sq_sqrt ht0.le
  have hρa : a < ρ := (sq_lt_sq₀ ha.le hρ0.le).mp (by rw [hρsq]; exact ht.1)
  have hρb : ρ < b := (sq_lt_sq₀ hρ0.le (ha.trans hab).le).mp (by rw [hρsq]; exact ht.2)
  have hmt : m t < B := (hm ht.2.le).trans_lt hmb
  have hν : ‖graphSlopeNormal n p‖ ≤ 1 := (graphSlopeNormal_unit hn p).le
  have hderG := hasDerivAt_sublevelVolume_of_interior_change radialSquared_contDiff.continuous.measurable
    ht.1 hchange hd.hasDerivAt
  have htotρ : sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (ρ^2) < T :=
    (sublevelVolume_mono _ _ (by rw [hρsq]; exact ht.2.le)).trans_lt htotal
  have hcompare := hcomp n hn (graphSlopeNormal n p) hν g hg ρ K (deriv m t) hρ0
    (hρb.trans hbs) hK (hρsq ▸ hderG) (htotρ.trans hT)
  have har := graphBallOrientedCost_le_disk cubeCenter hn hg p ρ
  have henergy : (∫ y in Metric.ball (0 : Plane) ρ, ‖gradient g y-p‖^2) ≤
      ∫ y in Metric.ball (0 : Plane) b, ‖gradient g y-p‖^2 :=
    setIntegral_mono_set (smooth_graph_relative_energy_integrable hg p b)
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hρb.le).eventuallyLE
  have hmono := bundleOrientedExcess_mono μ hν ha.le hρa.le
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hd1 : 2*K*(2*ρ)*deriv m t ≤ 2*K*(2*ρ)*(B/(b^2-a^2)) :=
    mul_le_mul_of_nonneg_left hder (by positivity)
  have hd2 : 2*K*(2*ρ)*(B/(b^2-a^2)) ≤ 2*K*(2*b)*(B/(b^2-a^2)) := by
    gcongr
  have hc1 : C*sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (ρ^2) ≤ C*T :=
    mul_le_mul_of_nonneg_left htotρ.le hC
  have heq : 4*K*b*B/(b^2-a^2) = 2*K*(2*b)*(B/(b^2-a^2)) := by ring
  rw [heq]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def graphBlend (χ g u : Plane → ℝ) (y : Plane) : ℝ :=
  g y + χ y * (u y-g y)

lemma graphBlend_contDiff {χ g u : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) : ContDiff ℝ (⊤ : ℕ∞) (graphBlend χ g u) :=
  hg.add (hχ.mul (hu.sub hg))

lemma graphBlend_eq_of_zero {χ g u : Plane → ℝ} {y : Plane} (h : χ y = 0) :
    graphBlend χ g u y = g y := by simp [graphBlend,h]

lemma graphBlend_eq_of_one {χ g u : Plane → ℝ} {y : Plane} (h : χ y = 1) :
    graphBlend χ g u y = u y := by simp [graphBlend,h]

lemma graphBlend_abs_le {χ g u : Plane → ℝ} {y : Plane} {H : ℝ}
    (hχ : χ y ∈ Icc 0 1) (hg : |g y| ≤ H) (hu : |u y| ≤ H) :
    |graphBlend χ g u y| ≤ H := by
  have he : graphBlend χ g u y = (1-χ y)*g y+χ y*u y := by dsimp [graphBlend]; ring
  rw [he]
  calc
    _ ≤ |(1-χ y)*g y|+|χ y*u y| := abs_add_le _ _
    _ = (1-χ y)*|g y|+χ y*|u y| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hχ.2),abs_of_nonneg hχ.1]
    _ ≤ (1-χ y)*H+χ y*H := add_le_add
      (mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr hχ.2)) (mul_le_mul_of_nonneg_left hu hχ.1)
    _ = H := by ring

lemma graphBlend_fderiv {χ g u : Plane → ℝ} {y : Plane}
    (hχ : DifferentiableAt ℝ χ y) (hg : DifferentiableAt ℝ g y)
    (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (graphBlend χ g u) y =
      (1-χ y) • fderiv ℝ g y + χ y • fderiv ℝ u y +
        (u y-g y) • fderiv ℝ χ y := by
  unfold graphBlend
  have hh := (hg.hasFDerivAt.add (hχ.hasFDerivAt.mul (hu.hasFDerivAt.sub hg.hasFDerivAt))).fderiv
  change fderiv ℝ (fun y ↦ g y + χ y*(u y-g y)) y = _ at hh
  dsimp only [Pi.sub_apply] at hh
  rw [hh]
  module

lemma norm_add_three_sq_le {X : Type*} [NormedAddCommGroup X] (a b c : X) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have h := (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

lemma graphBlend_relative_energy_pointwise {χ g u : Plane → ℝ} {y : Plane}
    (hχ : DifferentiableAt ℝ χ y) (hg : DifferentiableAt ℝ g y)
    (hu : DifferentiableAt ℝ u y) (hb : χ y ∈ Icc 0 1)
    (p : Plane →L[ℝ] ℝ) :
    ‖fderiv ℝ (graphBlend χ g u) y-p‖^2 ≤
      3*((1-χ y)^2*‖fderiv ℝ g y-p‖^2+‖fderiv ℝ u y-p‖^2+
        (u y-g y)^2*‖fderiv ℝ χ y‖^2) := by
  have he : fderiv ℝ (graphBlend χ g u) y-p =
      (1-χ y) • (fderiv ℝ g y-p)+χ y • (fderiv ℝ u y-p)+
        (u y-g y) • fderiv ℝ χ y := by
    rw [graphBlend_fderiv hχ hg hu]
    module
  rw [he]
  have h := norm_add_three_sq_le ((1-χ y) • (fderiv ℝ g y-p))
    (χ y • (fderiv ℝ u y-p)) ((u y-g y) • fderiv ℝ χ y)
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
  have hc : (χ y)^2*‖fderiv ℝ u y-p‖^2 ≤ ‖fderiv ℝ u y-p‖^2 := by
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [hb.1,hb.2])
  linarith

lemma graphBlend_relative_energy_cutoff {χ g u : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hb : ∀ y, χ y ∈ Icc 0 1)
    {D s b : ℝ} (hD : 0 ≤ D) (hd : ∀ y, ‖fderiv ℝ χ y‖ ≤ D)
    (hone : ∀ y ∈ Metric.ball (0 : Plane) s, χ y = 1)
    (p : Plane →L[ℝ] ℝ) :
    (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ (graphBlend χ g u) y-p‖^2) ≤
      3*((∫ y in Metric.ball (0 : Plane) b \ Metric.ball 0 s, ‖fderiv ℝ g y-p‖^2)+
        (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ u y-p‖^2)+
        D^2*(∫ y in Metric.ball (0 : Plane) b, (u y-g y)^2)) := by
  let B := Metric.ball (0 : Plane) b
  let S := Metric.ball (0 : Plane) s
  have hi (f : Plane → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
      IntegrableOn (fun y ↦ ‖fderiv ℝ f y-p‖^2) B :=
    ((((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) b)).mono_set Metric.ball_subset_closedBall
  have hid : IntegrableOn (fun y ↦ (u y-g y)^2) B :=
    (((hu.continuous.sub hg.continuous).pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) b)).mono_set Metric.ball_subset_closedBall
  have hind : IntegrableOn (Sᶜ.indicator (fun y ↦ ‖fderiv ℝ g y-p‖^2)) B :=
    (hi g hg).indicator measurableSet_ball.compl
  have hh : (∫ y in B, ‖fderiv ℝ (graphBlend χ g u) y-p‖^2) ≤
      ∫ y in B, 3*(Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y+
        ‖fderiv ℝ u y-p‖^2+D^2*(u y-g y)^2) := by
    apply integral_mono (hi _ (graphBlend_contDiff hχ hg hu))
      (((Integrable.add hind (hi u hu)).add (hid.const_mul _)).const_mul _)
    intro y
    have hp := graphBlend_relative_energy_pointwise
      (hχ.differentiable (by simp)).differentiableAt
      (hg.differentiable (by simp)).differentiableAt
      (hu.differentiable (by simp)).differentiableAt (hb y) p
    have ha : (1-χ y)^2*‖fderiv ℝ g y-p‖^2 ≤ Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y := by
      by_cases hy : y ∈ S
      · simp [indicator_of_notMem (show y ∉ Sᶜ from fun h ↦ h hy),hone y hy]
      · rw [indicator_of_mem hy]
        apply mul_le_of_le_one_left (sq_nonneg _)
        have hyb := hb y
        nlinarith [hyb.1,hyb.2]
    have hc : (u y-g y)^2*‖fderiv ℝ χ y‖^2 ≤ D^2*(u y-g y)^2 := by
      have hsq := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hd y)
      nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (u y-g y))]
    change ‖fderiv ℝ (graphBlend χ g u) y-p‖^2 ≤ 3*(Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y+‖fderiv ℝ u y-p‖^2+D^2*(u y-g y)^2)
    linarith
  calc
    _ ≤ _ := hh
    _ = _ := by
      rw [integral_const_mul,integral_add (f := fun y ↦ Sᶜ.indicator (fun z ↦ ‖fderiv ℝ g z-p‖^2) y+‖fderiv ℝ u y-p‖^2) (g := fun y ↦ D^2*(u y-g y)^2) (Integrable.add hind (hi u hu)) (hid.const_mul _),
        integral_add (μ := volume.restrict B) hind (hi u hu),integral_const_mul]
      rw [integral_indicator measurableSet_ball.compl,Measure.restrict_restrict measurableSet_ball.compl]
      rw [show Sᶜ ∩ B = Metric.ball (0 : Plane) b \ Metric.ball 0 s by
        ext y; simp [B,S,and_comm]]

end CubicTorus

end
end

end

end OAI
