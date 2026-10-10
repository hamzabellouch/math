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
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma normalWaveMetric_common_positive (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ x : NormalWaveSpace, ‖x‖ < r →
      0 < (normalWaveMetric g q x).det := by
  let G : NormalWaveParameter × NormalWaveSpace → Matrix (Fin 3) (Fin 3) ℝ :=
    fun w => normalWaveMetric g w.1 w.2
  have hG (i j : Fin 3) : ContDiff ℝ ∞ (fun w => G w i j) := contDiff_normalWaveMetric g i j
  let O := {w : NormalWaveParameter × NormalWaveSpace | 0 < (G w).det}
  have hO : IsOpen O := isOpen_lt continuous_const (contDiff_matrix_det G hG).continuous
  have hs : metricFrameSet g K ×ˢ {(0 : NormalWaveSpace)} ⊆ O := by
    rintro ⟨q,x⟩ ⟨hq,hx⟩
    have he : x = 0 := mem_singleton_iff.mp hx
    subst x
    change 0 < (normalWaveMetric g q 0).det
    rw [normalWaveMetric_zero g hq]
    simp
  obtain ⟨U,V,hU,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (metricFrameSet_isCompact g hK)
    isCompact_singleton hO hs
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton 0))
  refine ⟨r,hr,?_⟩
  intro q hq x hx
  change (q,x) ∈ O
  apply hUV
  refine ⟨hKU hq,hrV ?_⟩
  simpa only [Metric.mem_ball,dist_zero_right] using hx

theorem normalChartWave_residual_germ (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (q : NormalWaveParameter) (e : OpenPartialHomeomorph NormalWaveSpace NormalWaveSpace)
    (he : (e : NormalWaveSpace → NormalWaveSpace) =
      normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2))
    {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, normalWaveEquiv x ∈ e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (A : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ) (b : Fin 3 → (Fin 3 → ℝ) → ℂ)
    (lam : ℂ) {R : ℝ}
    (hp : ∀ v : NormalWaveSpace, ‖v‖ < R → 0 < (normalWaveMetric g q v).det)
    (hA : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ i j,
      A i j x = ((normalWaveMetric g q (normalWaveEquiv x))⁻¹ i j : ℂ))
    (hb : ∀ x, ‖normalWaveEquiv x‖ < R → ∀ j,
      b j x = (normalWaveFirstCoefficient g q (normalWaveEquiv x) j : ℂ))
    {x : Fin 3 → ℝ} (hx : normalWaveEquiv x ∈ e.source) (hxR : ‖normalWaveEquiv x‖ < R) :
    (fun y => complexLaplaceBeltrami g (normalChartWave e f) y + lam*normalChartWave e f y)
      =ᶠ[𝓝 (e (normalWaveEquiv x))] (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) A b f (normalWaveEquiv.symm (e.symm y)) +
          lam*f (normalWaveEquiv.symm (e.symm y))) := by
  have ht := e.map_source hx
  have hcont := (e.continuousAt_symm ht).norm
  have hR : ∀ᶠ y in 𝓝 (e (normalWaveEquiv x)), ‖e.symm y‖ < R := by
    apply hcont.eventually (gt_mem_nhds _)
    simpa only [e.left_inv hx] using hxR
  filter_upwards [e.open_target.mem_nhds ht,hR] with y hy hyR
  let v := normalWaveEquiv.symm (e.symm y)
  have hv : normalWaveEquiv v ∈ e.source := by
    simpa only [v,ContinuousLinearEquiv.apply_symm_apply] using e.map_target hy
  have hvR : ‖normalWaveEquiv v‖ < R := by
    simpa only [v,ContinuousLinearEquiv.apply_symm_apply] using hyR
  have hey : e (normalWaveEquiv v) = y := by
    simp only [v,ContinuousLinearEquiv.apply_symm_apply,e.right_inv hy]
  have hL := normalChartWave_laplacian g q e he hf hc hs hi hv (hp _ hvR)
  have hE := normalWavePiOperator_eq_extension g q hf A b v (hA v hvR) (hb v hvR)
  have hval := normalChartWave_apply e f hv
  rw [hey] at hL hval
  rw [hL,hE,hval]
end YauCounterexamples
end

end OAI
