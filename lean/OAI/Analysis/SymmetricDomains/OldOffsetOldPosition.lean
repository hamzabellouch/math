import Mathlib
import OAI.Analysis.SymmetricDomains.GoodNashBoundary

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

theorem analytic_chart_right_inverse_of_dimension {m N : ℕ} {V : Set (Affine N)}
    {a : Affine m} (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id)
    (hFV : ∀ᶠ z in 𝓝 a, F z ∈ V)
    (H : Affine m → Affine N) (J : Affine N → Affine m)
    (hH0 : H 0 = F a) (hH : AnalyticAt ℂ H 0) (hJ : AnalyticAt ℂ J (F a))
    (hJH : (J ∘ H) =ᶠ[𝓝 (0 : Affine m)] id)
    (hHJ : ∀ᶠ y in 𝓝[V] (F a), H (J y) = y) :
    ∀ᶠ y in 𝓝[V] (F a), F (G y) = y := by
  have hJ0 : J (F a) = 0 := by simpa only [Function.comp_apply,hH0,id_eq] using hJH.eq_of_nhds
  let A : Affine m → Affine m := J ∘ F
  have hA : AnalyticAt ℂ A a := hJ.comp hF
  have hA0 : A a = 0 := hJ0
  have htF : Tendsto F (𝓝 a) (𝓝[V] (F a)) := tendsto_nhdsWithin_iff.mpr ⟨hF.continuousAt,hFV⟩
  have hHA : (H ∘ A) =ᶠ[𝓝 a] F := htF hHJ
  have hH' : AnalyticAt ℂ H (A a) := hA0.symm ▸ hH
  have hdHA : (fderiv ℂ H (A a)).comp (fderiv ℂ A a) = fderiv ℂ F a :=
    ((hH'.differentiableAt.hasFDerivAt.comp a hA.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hHA.symm).unique hF.differentiableAt.hasFDerivAt
  have hdGF : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    ((hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm).unique (hasFDerivAt_id a)
  have hi : Function.Injective (fderiv ℂ A a) := by
    intro u v huv
    have hw : (fderiv ℂ F a) u = (fderiv ℂ F a) v := by
      rw [← hdHA]
      exact congrArg (fderiv ℂ H (A a)) huv
    have hx := congrArg (fderiv ℂ G (F a)) hw
    simpa only [← ContinuousLinearMap.comp_apply,hdGF,ContinuousLinearMap.id_apply] using hx
  let L := ((fderiv ℂ A a).toLinearMap.linearEquivOfInjective hi rfl).toContinuousLinearEquiv
  have hL : (L : Affine m →L[ℂ] Affine m) = fderiv ℂ A a := rfl
  obtain ⟨e,he,hes,hea⟩ := analytic_local_inverse hA L (hL.symm ▸ hA.differentiableAt.hasFDerivAt)
  have heAa : e a = A a := congrFun he a
  have hesym : e.symm (A a) = a := by rw [← heAa]; exact e.left_inv hes
  have hetarget : A a ∈ e.target := heAa ▸ e.map_source hes
  have het : Tendsto e.symm (𝓝 (A a)) (𝓝 a) := by
    simpa only [ContinuousAt,hesym] using hea.continuousAt
  let B : Affine N → Affine m := e.symm ∘ J
  have hB : Tendsto B (𝓝 (F a)) (𝓝 a) := het.comp hJ.continuousAt
  have hBHA : ∀ᶠ y in 𝓝 (F a), H (A (B y)) = F (B y) := hB hHA
  have hBGF : ∀ᶠ y in 𝓝 (F a), G (F (B y)) = B y := hB hGF
  have hJt : ∀ᶠ y in 𝓝 (F a), J y ∈ e.target :=
    hJ.continuousAt (e.open_target.mem_nhds hetarget)
  filter_upwards [hHJ,mem_nhdsWithin_of_mem_nhds hBHA,
    mem_nhdsWithin_of_mem_nhds hBGF,mem_nhdsWithin_of_mem_nhds hJt] with y hy hya hyb hyt
  have hAB : A (B y) = J y := by
    simpa only [he,B,Function.comp_apply] using e.right_inv hyt
  have hFB : F (B y) = y := by rw [← hya,hAB,hy]
  rw [hFB] at hyb
  rw [hyb,hFB]

theorem ProjectionNashChart.right_inverse_at {N m : ℕ} {V : Set (Affine N)}
    {p : Affine N} (c : ProjectionNashChart V p m) {a : Affine m}
    (ha : ‖complexRealEquiv m a‖ < c.radius)
    (H : Affine m → Affine N) (J : Affine N → Affine m)
    (hH0 : H 0 = c.inverse a) (hH : AnalyticAt ℂ H 0)
    (hJ : AnalyticAt ℂ J (c.inverse a))
    (hJH : (J ∘ H) =ᶠ[𝓝 (0 : Affine m)] id)
    (hHJ : ∀ᶠ y in 𝓝[V] (c.inverse a), H (J y) = y) :
    ∀ᶠ y in 𝓝[V] (c.inverse a), c.inverse (c.projection (y-p)) = y := by
  have hT : IsOpen {z : Affine m | ‖complexRealEquiv m z‖ < c.radius} :=
    isOpen_lt ((complexRealEquiv m).continuous.norm) continuous_const
  apply analytic_chart_right_inverse_of_dimension c.inverse (fun y => c.projection (y-p))
    (c.inverse_analytic a ha) ((c.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
    _ _ H J hH0 hH hJ hJH hHJ
  · filter_upwards [hT.mem_nhds ha] with z hz
    exact c.left_inverse z hz
  · filter_upwards [hT.mem_nhds ha] with z hz
    exact c.inverse_mem z hz

theorem NashNormalCoordinates.graph_germ_at {d m : ℕ}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine m} {a x : Fin d → ℝ}
    (c : NashNormalCoordinates B q a) (hx : x ∈ c.parameters.source)
    (hxb : c.parameters x ∈ ball 0 c.radius) :
    ∀ᶠ y in 𝓝 x, c.parameters y ∈ ball 0 c.radius ∧
      c.realCoordinates (q y-q a) = (c.parameters y,c.graph (c.parameters y)) := by
  have hs := c.parameters.open_source.mem_nhds hx
  have hb := (c.parameters.continuousAt hx).preimage_mem_nhds (isOpen_ball.mem_nhds hxb)
  filter_upwards [hs,hb] with y hy hyb
  refine ⟨hyb,?_⟩
  change complexGraphRealEquiv _ _ (c.coordinates (q y-q a)) = _
  simpa only [c.parameters.left_inv hy] using c.graph_identity (c.parameters y) hyb

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

noncomputable def oldPosition (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) : Affine m :=
  c.normal.realCoordinates.symm (s,c.normal.graph s)

noncomputable def oldParameter (c : NashBoundaryChart (m := m) U V B q) (z : Affine m) :=
  (c.normal.realCoordinates z).1

noncomputable def oldOffset (c : NashBoundaryChart (m := m) U V B q) (z : Affine m) :=
  (c.normal.realCoordinates z).2-c.normal.graph (c.oldParameter z)

@[simp] theorem oldParameter_oldPosition (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.oldParameter (c.oldPosition s) = s := by
  simp only [oldParameter,oldPosition,ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem oldOffset_oldPosition (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.oldOffset (c.oldPosition s) = 0 := by
  simp only [oldOffset,oldParameter,oldPosition,ContinuousLinearEquiv.apply_symm_apply,sub_self]

 theorem oldOffset_analyticAt (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) : AnalyticAt ℝ c.oldOffset (c.oldPosition s) := by
  have hC := c.normal.realCoordinates.toContinuousLinearMap.analyticAt (c.oldPosition s)
  have hp : AnalyticAt ℝ c.oldParameter (c.oldPosition s) := analyticAt_fst.comp hC
  have hφ : AnalyticAt ℝ c.normal.graph (c.oldParameter (c.oldPosition s)) := by
    simpa only [oldParameter_oldPosition] using c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)
  exact (analyticAt_snd.comp hC).sub (hφ.comp hp)

 theorem oldPosition_inverse (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.chart.inverse (c.oldPosition (c.normal.parameters x)) = q x := by
  simpa only [oldPosition,c.normal.parameters.left_inv hgood.1] using
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.2

 theorem oldPosition_projection (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.oldPosition (c.normal.parameters x) = c.chart.projection (q x-q c.center) := by
  have h := c.chart.left_inverse (c.oldPosition (c.normal.parameters x))
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.1
  rw [c.oldPosition_inverse hgood] at h
  exact h.symm

 theorem oldOffset_projection_germ (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) :
    (fun y => c.oldOffset (c.chart.projection (q y-q c.center))) =ᶠ[𝓝 x] fun _ => 0 := by
  have hg := c.normal.graph_germ_at hgood.1 (ball_subset_ball c.graphRadius_le hgood.2.1)
  have h0 : c.chart.projection (q c.center-q c.center) = 0 := by rw [sub_self,map_zero]
  filter_upwards [hg] with y hy
  simp only [h0,sub_zero] at hy
  simp only [oldOffset,oldParameter,hy.2,sub_self]
end NashBoundaryChart
end Release061

end

end OAI
