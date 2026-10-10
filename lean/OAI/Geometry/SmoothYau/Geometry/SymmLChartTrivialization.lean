import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SphericalBaseProfileRadius

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
abbrev MetricForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ
abbrev TangentForm (x : M) := TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ

local instance tensorDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance tensorDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance tensorFormNorm : NormedAddCommGroup (MetricForm E) := inferInstanceAs
  (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance tensorFormSpace : NormedSpace ℝ (MetricForm E) := inferInstanceAs
  (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
local instance tensorTangentDualAdd (x : M) : IsTopologicalAddGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  ContinuousLinearMap.isTopologicalAddGroup
local instance tensorTangentDualSmul (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
local instance tensorTangentFormAdd (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) :=
  ContinuousLinearMap.isTopologicalAddGroup
local instance tensorTangentFormSmul (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance

def chartFormTrivialization (p : M) := trivializationAt (MetricForm E) (TangentForm (E:=E)) p
omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormTrivialization_baseSet (p : M) :
    (chartFormTrivialization (E:=E) p).baseSet = (chartAt E p).source := by
  simp [chartFormTrivialization,hom_trivializationAt_baseSet,TangentBundle.trivializationAt_baseSet]
instance chartFormTrivialization_mem (p : M) :
    MemTrivializationAtlas (chartFormTrivialization (E:=E) p) := inferInstanceAs
      (MemTrivializationAtlas (trivializationAt (MetricForm E) (TangentForm (E:=E)) p))

def chartFormPush (p : M) (f : E → MetricForm E) (x : M) : TangentForm (E:=E) x :=
  (chartFormTrivialization (E:=E) p).symmL ℝ x (manifoldChartPush p f x)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_zero (p : M) {f : E → MetricForm E} {x : M}
    (hx : manifoldChartPush p f x = 0) : chartFormPush p f x = 0 := by
  unfold chartFormPush
  rw [hx]
  exact ((chartFormTrivialization (E:=E) p).symmL ℝ x).map_zero

omit [FiniteDimensional ℝ E] in
lemma contMDiff_chartFormPush (p : M) {f : E → MetricForm E}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt E p).target) :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,MetricForm E)) ∞
      (fun x => TotalSpace.mk' (MetricForm E) x (chartFormPush p f x)) := by
  let : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
    fun x => (tensorTangentDualAdd (E:=E) x).toContinuousAdd
  intro x
  by_cases hx : x ∈ (chartAt E p).source
  · have hx' : x ∈ (chartFormTrivialization (E:=E) p).baseSet := by
      rwa [chartFormTrivialization_baseSet]
    rw [(chartFormTrivialization (E:=E) p).contMDiffAt_section_iff hx']
    apply (contMDiff_manifoldChartPush p hf hc hs x).congr_of_eventuallyEq
    filter_upwards [(chartFormTrivialization (E:=E) p).open_baseSet.mem_nhds hx'] with y hy
    simp only [chartFormPush,Trivialization.symmL_apply _ hy,Trivialization.apply_mk_symm _ hy]
  · have ht : x ∉ tsupport (manifoldChartPush p f) := by
      intro hn
      obtain ⟨y,hy,hxy⟩ := manifoldChartPush_tsupport p hc hs hn
      exact hx (hxy ▸ (chartAt E p).map_target (hs hy))
    apply (contMDiffAt_zeroSection ℝ (E:=TangentForm (E:=E) (M:=M))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
    exact congrArg (TotalSpace.mk' (MetricForm E) y) (chartFormPush_zero p hy)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_trivialization (p : M) {f : E → MetricForm E} {x : M}
    (hx : x ∈ (chartAt E p).source) :
    (chartFormTrivialization (E:=E) p ⟨x,chartFormPush p f x⟩).2 = f ((chartAt E p) x) := by
  have hx' : x ∈ (chartFormTrivialization (E:=E) p).baseSet := by
    rwa [chartFormTrivialization_baseSet]
  simp only [chartFormPush,Trivialization.symmL_apply _ hx',Trivialization.apply_mk_symm _ hx',
    manifoldChartPush,Set.indicator_of_mem hx,Function.comp_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_eq_zero_of_not_source (p : M) {f : E → MetricForm E} {x : M}
    (hx : x ∉ (chartAt E p).source) : chartFormPush p f x = 0 := by
  exact chartFormPush_zero p (by simp [manifoldChartPush,hx])

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormTrivialization_pairing (p : M) {x : M} (hx : x ∈ (chartAt E p).source)
    (B : TangentForm (E:=E) x) (v w : E) :
    (chartFormTrivialization (E:=E) p ⟨x,B⟩).2 v w =
      B ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x v)
        ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symm x w) := by
  have ht : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  simp only [chartFormTrivialization,hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ ht ht (by simp)]
  simp

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_pairing (p : M) {f : E → MetricForm E} {x : M}
    (hx : x ∈ (chartAt E p).source) (v w : TangentSpace 𝓘(ℝ,E) x) :
    chartFormPush p f x v w = f ((chartAt E p) x)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,v⟩).2)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,w⟩).2) := by
  have ht : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hh := congrArg (fun B : MetricForm E => B
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,v⟩).2)
      ((trivializationAt E (TangentSpace 𝓘(ℝ,E)) p ⟨x,w⟩).2))
    (chartFormPush_trivialization (f:=f) p hx)
  simpa only [chartFormTrivialization_pairing p hx,Trivialization.symm_apply_apply_mk _ ht] using hh

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartFormPush_symm (p : M) {f : E → MetricForm E}
    (hf : ∀ x v w, f x v w = f x w v) (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    chartFormPush p f x v w = chartFormPush p f x w v := by
  by_cases hx : x ∈ (chartAt E p).source
  · rw [chartFormPush_pairing p hx,chartFormPush_pairing p hx,hf]
  · rw [chartFormPush_eq_zero_of_not_source p hx]
    rfl

def symmetrizeMetricForm : MetricForm E →L[ℝ] MetricForm E :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ (MetricForm E) +
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap)
lemma symmetrizeMetricForm_apply (B : MetricForm E) (v w : E) :
    symmetrizeMetricForm B v w = (B v w+B w v)/2 := by
  change (1/2:ℝ)*(B v w+B w v) = _
  ring
lemma symmetrizeMetricForm_symm (B : MetricForm E) (v w : E) :
    symmetrizeMetricForm B v w = symmetrizeMetricForm B w v := by
  simp only [symmetrizeMetricForm_apply,add_comm]
lemma symmetrizeMetricForm_eq_self (B : MetricForm E) (hB : ∀ v w, B v w=B w v) :
    symmetrizeMetricForm B = B := by
  ext v w
  rw [symmetrizeMetricForm_apply,hB v w]
  ring
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma symmL_chart_trivialization (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symmL ℝ ((chartAt E p).symm y) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y := by
  have h := TangentBundle.symmL_trivializationAt (I:=𝓘(ℝ,E)) ((chartAt E p).map_target hy)
  have h' : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).symmL ℝ ((chartAt E p).symm y) =
      (show E →L[ℝ] E from mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm
        ((chartAt E p) ((chartAt E p).symm y))) := by
    simpa [extChartAt] using h
  exact h'.trans (congrArg (fun z : E => (show E →L[ℝ] E from
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm z)) ((chartAt E p).right_inv hy))

omit [T2Space M] in
lemma chartFormTrivialization_metric (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    (chartFormTrivialization (E:=E) p ⟨(chartAt E p).symm y,g.inner ((chartAt E p).symm y)⟩).2 =
      chartMetricForm g p y := by
  have hx : (chartAt E p).symm y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using (chartAt E p).map_target hy
  ext v w
  rw [chartFormTrivialization_pairing p ((chartAt E p).map_target hy),chartMetricForm_pairing]
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (symmL_chart_trivialization p hy)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (symmL_chart_trivialization p hy)
  have hv := (Trivialization.symmL_apply (R:=ℝ) _ hx v).symm.trans hv
  have hw := (Trivialization.symmL_apply (R:=ℝ) _ hx w).symm.trans hw
  exact congrArg₂ (fun a b => g.inner ((chartAt E p).symm y) a b) hv hw

end YauCounterexamples
end

end OAI
