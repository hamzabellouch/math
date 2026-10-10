import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.NormalChartWave

namespace OAI

noncomputable section
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
open Set Filter Matrix
open scoped Topology ContDiff
namespace YauCounterexamples
section MetricLocality
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_germ (b : Module.Basis ι ℝ E)
    (G : E → Matrix ι ι ℝ) {u v : E → ℝ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    coordinateMetricLaplacian b G u x = coordinateMetricLaplacian b G v x := by
  unfold coordinateMetricLaplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => coordinateMetricFlux b G u y i) =ᶠ[𝓝 x]
      (fun y => coordinateMetricFlux b G v y i) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [coordinateMetricFlux,hy]
  rw [he.fderiv_eq]

omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_zero (b : Module.Basis ι ℝ E) (G : E → Matrix ι ι ℝ) (x : E) :
    coordinateMetricLaplacian b G (0 : E → ℝ) x = 0 := by
  simp [coordinateMetricLaplacian,coordinateMetricFlux]

lemma complexLaplaceBeltrami_self_germ (g : SmoothMetric E E)
    {u v : E → ℂ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    complexLaplaceBeltrami g u x = complexLaplaceBeltrami g v x := by
  apply Complex.ext
  · simp only [complexLaplaceBeltrami,laplaceBeltrami_self]
    exact coordinateMetricLaplacian_germ _ _ (h.fun_comp Complex.re)
  · simp only [complexLaplaceBeltrami,laplaceBeltrami_self]
    exact coordinateMetricLaplacian_germ _ _ (h.fun_comp Complex.im)

lemma complexLaplaceBeltrami_self_zero (g : SmoothMetric E E) (x : E) :
    complexLaplaceBeltrami g (0 : E → ℂ) x = 0 := by
  apply Complex.ext <;>
    change laplaceBeltrami g (0 : E → ℝ) x = 0 <;>
    rw [laplaceBeltrami_self,coordinateMetricLaplacian_zero]

lemma complexLaplaceBeltrami_residual_tsupport (g : SmoothMetric E E) (u : E → ℂ) (lam : ℂ) :
    tsupport (fun y => complexLaplaceBeltrami g u y + lam*u y) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he := notMem_tsupport_iff_eventuallyEq.mp hn
  have hz := complexLaplaceBeltrami_self_germ g he
  rw [complexLaplaceBeltrami_self_zero] at hz
  apply hx
  change complexLaplaceBeltrami g u x + lam*u x = 0
  rw [hz,he.eq_of_nhds]
  simp
end MetricLocality

lemma canonicalCutoffWave_tsupport
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (s : ℂ) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (m D : ℕ) (n : ℝ) :
    tsupport (canonicalCutoffWave A b s z Q ζ m D n) ⊆ tsupport ζ :=
  closure_mono (smoothFiniteWave_cutoff_support _ _ _ _ _)

lemma canonicalCutoffWave_compact
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (s : ℂ) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : HasCompactSupport ζ) (m D : ℕ) (n : ℝ) :
    HasCompactSupport (canonicalCutoffWave A b s z Q ζ m D n) :=
  smoothFiniteWave_cutoff_compact _ _ _ hζ _ _

lemma normalChartWave_tsupport (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    {f : (Fin 3 → ℝ) → ℂ} (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source) :
    tsupport (normalChartWave e f) ⊆ (fun x => e (normalWaveEquiv x)) '' tsupport f := by
  have hc' := hc.comp_homeomorph normalWaveEquiv.symm.toHomeomorph
  have hs' : tsupport (f ∘ normalWaveEquiv.symm) ⊆ e.source := by
    change tsupport (f ∘ normalWaveEquiv.symm.toHomeomorph) ⊆ e.source
    rw [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph]
    intro y hy
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hs (normalWaveEquiv.symm y) hy
  intro y hy
  obtain ⟨x,hx,rfl⟩ := smoothChartPush_tsupport e hc' hs' hy
  refine ⟨normalWaveEquiv.symm x,?_,by simp⟩
  rwa [tsupport_comp_eq_preimage f normalWaveEquiv.symm.toHomeomorph] at hx

lemma normalChartWave_germ (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (f : (Fin 3 → ℝ) → ℂ) {y : NormalWaveSpace} (hy : y ∈ e.target) :
    normalChartWave e f =ᶠ[𝓝 y] (fun z => f (normalWaveEquiv.symm (e.symm z))) := by
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact Set.indicator_of_mem hz _
end YauCounterexamples
end

end OAI
