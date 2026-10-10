import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.BilinearCoordinateMatrixPosDef

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def smoothChartPush (e : OpenPartialHomeomorph E F) (f : E → V) : F → V :=
  e.target.indicator (f ∘ e.symm)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_apply (e : OpenPartialHomeomorph E F) (f : E → V)
    {x : E} (hx : x ∈ e.source) : smoothChartPush e f (e x) = f x := by
  simp only [smoothChartPush,Set.indicator_of_mem (e.map_source hx),Function.comp_apply,
    e.left_inv hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_support (e : OpenPartialHomeomorph E F) (f : E → V) :
    Function.support (smoothChartPush e f) ⊆ e '' tsupport f := by
  intro y hy
  have ht : y ∈ e.target := by
    by_contra hh
    exact hy (by simp [smoothChartPush,hh])
  refine ⟨e.symm y, subset_closure ?_,e.right_inv ht⟩
  simpa only [smoothChartPush,Set.indicator_of_mem ht,Function.comp_apply,
    Function.mem_support] using hy

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_tsupport (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : HasCompactSupport f) (hsub : tsupport f ⊆ e.source) :
    tsupport (smoothChartPush e f) ⊆ e '' tsupport f := by
  apply closure_minimal (smoothChartPush_support e f)
  exact (hf.image_of_continuousOn (e.continuousOn.mono hsub)).isClosed

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ V] in
lemma smoothChartPush_compact (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : HasCompactSupport f) (hsub : tsupport f ⊆ e.source) :
    HasCompactSupport (smoothChartPush e f) :=
  (hf.image_of_continuousOn (e.continuousOn.mono hsub)).of_isClosed_subset
    isClosed_closure (smoothChartPush_tsupport e hf hsub)

lemma contDiff_smoothChartPush (e : OpenPartialHomeomorph E F) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hsub : tsupport f ⊆ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (smoothChartPush e f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ e.target
  · have hg : smoothChartPush e f =ᶠ[𝓝 y] f ∘ e.symm := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact Set.indicator_of_mem hz _
    exact (hf.contDiffAt.comp y ((hi y hy).contDiffAt (e.open_target.mem_nhds hy))).congr_of_eventuallyEq hg
  · have hn : y ∉ e '' tsupport f := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hsub hx))
    have hs : y ∉ tsupport (smoothChartPush e f) := fun h => hn (smoothChartPush_tsupport e hc hsub h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hs)

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

def normalChartWave (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (f : (Fin 3 → ℝ) → ℂ) : NormalWaveSpace → ℂ :=
  smoothChartPush e (f ∘ normalWaveEquiv.symm)

lemma normalChartWave_compact (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    {f : (Fin 3 → ℝ) → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source) :
    HasCompactSupport (normalChartWave e f) := by
  apply smoothChartPush_compact e (hc.comp_homeomorph normalWaveEquiv.symm.toHomeomorph)
  change tsupport (f ∘ normalWaveEquiv.symm.toHomeomorph) ⊆ e.source
  rw [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph]
  intro x hx
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (normalWaveEquiv.symm x) hx

lemma contDiff_normalChartWave (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (normalChartWave e f) := by
  apply contDiff_smoothChartPush e (hf.comp normalWaveEquiv.symm.contDiff)
    (hc.comp_homeomorph normalWaveEquiv.symm.toHomeomorph) _ hi
  change tsupport (f ∘ normalWaveEquiv.symm.toHomeomorph) ⊆ e.source
  rw [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph]
  intro x hx
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (normalWaveEquiv.symm x) hx

lemma normalChartWave_apply (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (f : (Fin 3 → ℝ) → ℂ) {x : Fin 3 → ℝ} (hx : normalWaveEquiv x ∈ e.source) :
    normalChartWave e f (e (normalWaveEquiv x)) = f x := by
  simpa only [normalChartWave,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using
    smoothChartPush_apply e (f ∘ normalWaveEquiv.symm) hx

theorem normalChartWave_laplacian (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : (e : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) {x : Fin 3 → ℝ}
    (hx : normalWaveEquiv x ∈ e.source)
    (hp : 0 < (normalWaveMetric g q (normalWaveEquiv x)).det) :
    complexLaplaceBeltrami g (normalChartWave e f) (e (normalWaveEquiv x)) =
      normalWavePiOperator g q f x := by
  have hu := contDiff_normalChartWave e hf hc hs hi
  have h1 : (normalChartWave e f ∘
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
      =ᶠ[𝓝 (normalWaveEquiv x)] (f ∘ normalWaveEquiv.symm) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    change normalChartWave e f (normalJetMap _ _ _ y) = f (normalWaveEquiv.symm y)
    rw [←he]
    exact smoothChartPush_apply e (f ∘ normalWaveEquiv.symm) hy
  have h2 := (waveCoordinateOperator_congr_eventually
    (EuclideanSpace.basisFun (Fin 3) ℝ)
    (fun i j y => ((normalWaveMetric g q y)⁻¹ i j : ℂ))
    (fun j y => (normalWaveFirstCoefficient g q y j : ℂ)) h1).eq_of_nhds
  have h3 := complexLaplaceBeltrami_normal_coordinates g q
    (hu.of_le (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt hp
  rw [←he] at h3 h2
  exact h3.symm.trans h2



end YauCounterexamples
end

end OAI
