import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.LocalDiffeomorphismDetNeZero
import OAI.Geometry.SmoothYau.Estimates.CutoffPullbackSobolevBound
import OAI.Geometry.SmoothYau.Smoothness.ConstantComplexProductJetBound

namespace OAI

noncomputable section
namespace YauCounterexamples
section
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_controlled_coordinate_extension (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set E} (hK : IsCompact K) (hs : K ⊆ e.source) :
    ∃ ψ : E → E, ContDiff ℝ ∞ ψ ∧ e =ᶠ[𝓝ˢ K] ψ ∧ Set.InjOn ψ K ∧
      ∃ J : ℝ≥0, ∀ x ∈ K, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ ψ x).det| := by
  obtain ⟨ψ, hψ, heq⟩ := smooth_extension_near_compact hK e.open_source hs he
  have heqx (x : E) (hx : x ∈ K) : (e : E → E) =ᶠ[𝓝 x] ψ :=
    heq.filter_mono (nhds_le_nhdsSet hx)
  refine ⟨ψ, hψ, heq, ?_, ?_⟩
  · intro x hx y hy hxy
    apply e.injOn (hs hx) (hs hy)
    simpa only [(heqx x hx).eq_of_nhds, (heqx y hy).eq_of_nhds] using hxy
  · apply compact_jacobian_bound hK hψ
    intro x hx
    rw [← (heqx x hx).fderiv_eq]
    exact local_diffeomorphism_det_ne_zero e he he' (hs hx)


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma contMDiff_complex_mul {η χ : M → ℂ}
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η * χ) :=
  ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.comp hη).clm_apply hχ

omit [T2Space M] in

theorem chartLift_localization_bound (p q : M) (η χ : M → ℂ)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ (chartAt E p).source)
    (hηm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hχs : tsupport χ ⊆ (chartAt E q).source)
    (hχm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(E, ℂ),
      ‖schwartzToSobolev (2 * (k : ℝ))
        (chartSchwartz p η (chartLift q χ f) hηc hηs hηm
          (contMDiff_chartLift q χ hχs hχm (f.smooth ⊤)))‖ ≤
        C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖ := by
  let κ := chartLocalize (E := E) p (η * χ) (fun _ => 1)
  have hpc : HasCompactSupport (η * χ) := hηc.mul_right
  have hps : tsupport (η * χ) ⊆ (chartAt E p).source := tsupport_mul_subset_left.trans hηs
  have hκc : HasCompactSupport κ := hasCompactSupport_chartLocalize p _ _ hpc hps
  have hκm : ContDiff ℝ ∞ κ := contDiff_chartLocalize p _ _ hpc hps
    (contMDiff_complex_mul hηm hχm) contMDiff_const
  let e := (chartAt E p).symm.trans (chartAt E q)
  have he : ContDiffOn ℝ ∞ e e.source := contDiffOn_chartTransition p q
  have he' : ContDiffOn ℝ ∞ e.symm e.target := contDiffOn_chartTransition q p
  have hκs : tsupport κ ⊆ e.source := chart_overlap_cutoff_support p q η χ hηc hηs hχs
  obtain ⟨ψ, hψ, heψ, hψinj, J, hJ⟩ := exists_controlled_coordinate_extension e he he' hκc hκs
  obtain ⟨C, hC, hb⟩ := cutoffPullback_sobolev_bound κ hκc hκm ψ hψ hψinj J hJ k
  refine ⟨C, hC, fun f => ?_⟩
  have hid : chartSchwartz p η (chartLift q χ f) hηc hηs hηm
      (contMDiff_chartLift q χ hχs hχm (f.smooth ⊤)) = cutoffPullback κ hκc hκm ψ hψ f := by
    ext y
    change chartLocalize p η (chartLift q χ f) y = κ y * f (ψ y)
    rw [chartLocalize_chartLift]
    change κ y * f (e y) = κ y * f (ψ y)
    by_cases hy : y ∈ tsupport κ
    · rw [(heψ.filter_mono (nhds_le_nhdsSet hy)).eq_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]
  rw [hid]
  exact hb f



end YauCounterexamples
end

end OAI
