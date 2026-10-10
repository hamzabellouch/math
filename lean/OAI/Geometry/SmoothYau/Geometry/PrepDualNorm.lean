import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.FlowInitialFderiv
import OAI.Geometry.SmoothYau.Smoothness.PulledGradient

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance prepDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance prepDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance prepFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance prepFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

omit [FiniteDimensional ℝ E] in
lemma continuous_profileRankOne {X : Type*} [TopologicalSpace X]
    {l : X → E →L[ℝ] ℝ} (hl : Continuous l) : Continuous (fun x => profileRankOne (l x)) :=
  ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp hl).clm_apply hl

omit [FiniteDimensional ℝ E] in
lemma continuous_metricProfileTraceForm_comp {X : Type*} [TopologicalSpace X]
    {B H : X → CoordinateForm E} {a : X → E}
    (hB : Continuous B) (hH : Continuous H) (ha : Continuous a) :
    Continuous (fun x => metricProfileTraceForm (B x) (H x) (a x)) := by
  unfold metricProfileTraceForm
  exact (((hH.clm_apply ha).clm_apply ha).smul hB).add
    ((continuous_const.add ((hB.clm_apply ha).clm_apply ha)).smul hH)

lemma coordinateMetricGradient_ne_zero_dual (g : SmoothMetric E E) (u : E → ℝ) (x : E)
    (ha : coordinateMetricGradient g u x ≠ 0) :
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0 := by
  intro h
  have hd : fderiv ℝ u x = 0 := (InnerProductSpace.toDual ℝ E).symm.injective
    (by simpa only [map_zero] using h)
  apply ha
  simp only [coordinateMetricGradient,hd,map_zero]

theorem exists_actual_preparation_neighborhood (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {p : E}
    (ha : coordinateMetricGradient g u p ≠ 0) (hs : actualProfileStrict g u p) :
    ∃ (W : Set E) (s : E → ℝ) (C : ℝ), IsOpen W ∧ p ∈ W ∧
      ContDiff ℝ ∞ s ∧ 0 < C ∧ ∀ x ∈ W,
        fderiv ℝ s x ≠ 0 ∧ fderiv ℝ s x (coordinateMetricGradient g u x) = 0 ∧
        ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0) ∧
        (∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
        (∀ c ∈ Icc C (2*C), quadraticPlaneFull
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) := by
  obtain ⟨l,hl,hla,hlS,C₀,hlF⟩ := exists_actual_preparation_covector hd g u p ha hs
  obtain ⟨O,s₀,hOo,hOp,hs₀,hs₀p,hs₀d,hfirst⟩ :=
    smooth_first_integral (contDiff_coordinateMetricGradient g hu) ha l hl hla
  obtain ⟨s,hs,he⟩ := smooth_extension_near_compact isCompact_singleton hOo
    (singleton_subset_iff.mpr hOp) hs₀
  have he' : s₀ =ᶠ[𝓝 p] s := by simpa only [nhdsSet_singleton] using he
  have hsp : fderiv ℝ s p = l := by rw [←he'.fderiv_eq (𝕜:=ℝ),hs₀d]
  have hf : ∀ᶠ x in 𝓝 p, fderiv ℝ s x ≠ 0 ∧
      fderiv ℝ s x (coordinateMetricGradient g u x) = 0 := by
    filter_upwards [he'.fderiv (𝕜:=ℝ),hOo.mem_nhds hOp] with x hx hxO
    simpa only [←hx] using hfirst x hxO
  let C : ℝ := C₀+1
  have hC : 0 < C := by dsimp [C]; positivity
  let q : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)
  have hq : Continuous q := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hu.continuous_fderiv (by simp))
  have hqn : q p ≠ 0 := coordinateMetricGradient_ne_zero_dual g u p ha
  let T : E × ℝ → CoordinateForm E := fun z => metricProfileTraceForm
    (selfMetricFlat g z.1) (actualCoordinateHessian g u z.1+z.2 • profileRankOne (fderiv ℝ s z.1))
    (coordinateMetricGradient g u z.1)
  have hH : Continuous (actualCoordinateHessian g u) :=
    continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hu
  have hT : Continuous T := continuous_metricProfileTraceForm_comp
    ((contDiff_selfMetricFlat g).continuous.comp continuous_fst)
    ((hH.comp continuous_fst).add (continuous_snd.smul
      (continuous_profileRankOne ((hs.continuous_fderiv (by simp)).comp continuous_fst))))
    ((contDiff_coordinateMetricGradient g hu).continuous.comp continuous_fst)
  have hmap : Continuous (fun z : E × ℝ => (T z,q z.1)) := hT.prodMk (hq.comp continuous_fst)
  have hstrict : ∀ᶠ x in 𝓝 p, ∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict (T (x,c)) (q x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro c hc
    have hp : quadraticPlaneStrict (T (p,c)) (q p) := by
      dsimp only [T,q]
      rw [hsp]
      exact hlS c
    exact (quadraticPlaneStrict_eventually hqn hp).filter_mono hmap.continuousAt
  have hfull : ∀ᶠ x in 𝓝 p, ∀ c ∈ Icc C (2*C), quadraticPlaneFull (T (x,c)) (q x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro c hc
    have hp : quadraticPlaneFull (T (p,c)) (q p) := by
      dsimp only [T,q]
      rw [hsp]
      apply hlF c
      have hh : (C₀:ℝ) < C := by dsimp [C]; linarith
      exact hh.le.trans hc.1
    exact (hmap.continuousAt (x:=(p,c))).eventually (isOpen_quadraticPlaneFull.mem_nhds hp)
  obtain ⟨W,hW,hWo,hWp⟩ := _root_.mem_nhds_iff.mp
    (hf.and ((hq.continuousAt.eventually_ne hqn).and (hstrict.and hfull)))
  exact ⟨W,s,C,hWo,hWp,hs,hC,fun x hx =>
    ⟨(hW hx).1.1,(hW hx).1.2,(hW hx).2.1,(hW hx).2.2.1,(hW hx).2.2.2⟩⟩

end YauCounterexamples

end

end OAI
