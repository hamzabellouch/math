import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ExistsMetricPatchInverse

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

structure LocalMetricInverse (g : SmoothMetric E M) (p : M) (s : ℝ)
    (hs : Module.finrank ℝ E < 2 * s) where
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_pos : 0 < bound
  in_target : Metric.closedBall ((chartAt E p) p) radius ⊆ (chartAt E p).target
  inverse : (α : ℝ) → 1 ≤ α →
    FourierSobolevSpace E ℂ s →L[ℂ] FourierSobolevSpace E ℂ (s + 2)
  norm_bound : ∀ (α : ℝ) (hα : 1 ≤ α), ‖inverse α hα‖ ≤ bound
  half_bound : ∀ (α : ℝ) (hα : 1 ≤ α) f,
    ‖sobolevInclusion (s + 2) (s + 1) (by linarith) (inverse α hα f)‖ ≤
      bound * (Real.sqrt α)⁻¹ * ‖f‖
  equation : ∀ (α : ℝ) (hα : 1 ≤ α) (ht : Module.finrank ℝ E < 2 * (s + 2)) f x, ‖x‖ ≤ 1 →
    (α : ℂ) * sobolevRepresentative ht (inverse α hα f) x -
      (∑ i, ∑ j, ((metricCoefficients g p ((chartAt E p) p + radius • x))⁻¹ i j : ℂ) *
        fderiv ℝ (fun y => fderiv ℝ (sobolevRepresentative ht (inverse α hα f) : E → ℂ)
          y (Module.finBasis ℝ E j)) x (Module.finBasis ℝ E i)) -
      (radius : ℂ) * ∑ i, (metricFirstCoefficient g p i ((chartAt E p) p + radius • x) : ℂ) *
        fderiv ℝ (sobolevRepresentative ht (inverse α hα f) : E → ℂ) x (Module.finBasis ℝ E i) =
      sobolevRepresentative hs f x

theorem nonempty_localMetricInverse (g : SmoothMetric E M) (p : M)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) : Nonempty (LocalMetricInverse g p s hs) := by
  obtain ⟨r, C, hr, hC, ht, hR⟩ := exists_metric_patch_inverse g p hs
  choose R hRnorm hRhalf hReq using hR
  exact ⟨⟨r, hr, C, hC, ht, R, hRnorm, hRhalf, hReq⟩⟩

def metricInversePatch {g : SmoothMetric E M} {p : M} {s : ℝ}
    {hs : Module.finrank ℝ E < 2 * s} (D : LocalMetricInverse g p s hs) : Set M :=
  (chartAt E p).source ∩ (chartAt E p) ⁻¹' Metric.ball ((chartAt E p) p) (D.radius / 2)

lemma isOpen_metricInversePatch {g : SmoothMetric E M} {p : M} {s : ℝ}
    {hs : Module.finrank ℝ E < 2 * s} (D : LocalMetricInverse g p s hs) :
    IsOpen (metricInversePatch D) :=
  (chartAt E p).isOpen_inter_preimage Metric.isOpen_ball

lemma mem_metricInversePatch {g : SmoothMetric E M} {p : M} {s : ℝ}
    {hs : Module.finrank ℝ E < 2 * s} (D : LocalMetricInverse g p s hs) :
    p ∈ metricInversePatch D :=
  ⟨mem_chart_source E p, Metric.mem_ball_self (half_pos D.radius_pos)⟩

theorem exists_compact_metric_patches [T2Space M] [CompactSpace M]
    (g : SmoothMetric E M) {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    ∃ (t : Finset M) (D : ∀ i : t, LocalMetricInverse g (i : M) s hs)
      (η χ ψ : t → M → ℂ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i)) ∧
      (∀ x, ∑ i, η i x = 1) ∧
      (∀ i, tsupport (η i) ⊆ metricInversePatch (D i)) ∧
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ metricInversePatch (D i)) ∧
      (∀ i, χ i =ᶠ[𝓝ˢ (tsupport (η i))] 1) ∧
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ metricInversePatch (D i)) ∧
      (∀ i, ψ i =ᶠ[𝓝ˢ (tsupport (χ i))] 1) := by
  classical
  let D : ∀ p : M, LocalMetricInverse g p s hs := fun p =>
    (nonempty_localMetricInverse g p hs).some
  obtain ⟨t, ρ, hρ⟩ := exists_finite_patch_partition (E := E)
    (fun p => metricInversePatch (D p)) (fun p => isOpen_metricInversePatch (D p))
    (fun p => mem_metricInversePatch (D p))
  let η : t → M → ℂ := fun i x => (ρ i x : ℂ)
  have hηm (i : t) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i) :=
    Complex.ofRealCLM.contMDiff.comp (ρ i).contMDiff
  have hηs (i : t) : tsupport (η i) ⊆ metricInversePatch (D (i : M)) := by
    apply (closure_mono (show support (η i) ⊆ support (ρ i) from ?_)).trans (hρ i)
    intro x hx
    exact fun hh => hx (by simp [η, hh])
  choose χ hχm hχs hχη using fun (i : t) => exists_patch_buffer (E := E)
    (isOpen_metricInversePatch (D (i : M))) (hηs i)
  choose ψ hψm hψs hψχ using fun (i : t) => exists_patch_buffer (E := E)
    (isOpen_metricInversePatch (D (i : M))) (hχs i)
  refine ⟨t, fun i => D (i : M), η, χ, ψ, hηm, ?_, hηs, hχm, hχs, hχη,
    hψm, hψs, hψχ⟩
  intro x
  change ∑ i : t, (ρ i x : ℂ) = 1
  rw [← Complex.ofReal_sum]
  exact_mod_cast (by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x))
end YauCounterexamples


end

end OAI
