import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.VaryingSpectralResolventBase

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem represented_weighted_quintic_smooth (hd : Module.finrank ℝ E = 3)
    {b s u : M → ℝ} (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ s) (hpos : ∀ x, 0 < b x)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (Λ : ℝ)
    (he : ∀ x, weightedLaplacian g b u x = Λ * b x ^ 3 * u x ^ 5 - Λ * s x * u x)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = fun x => (u x : ℂ)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u := by
  let g' := conformalMetric g b hb hpos
  let B := (nonempty_compactMetricAtlas g' k hs).some
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by push_cast; linarith
  let v' := A.transferAcross B (k + 1) v
  have hv' : (B.representative (2 * ((k + 1 : ℕ) : ℝ)) v' : M → ℂ) = fun x => (u x : ℂ) := by
    change (B.representative _ (A.transferAcross B (k + 1) v) : M → ℂ) = _
    rw [A.transferAcross_representative B (k + 1) ht]
    exact hv
  have ha1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => -(Λ * s x / b x ^ 3)) :=
    ((contMDiff_const.mul hsmooth).div₀ (hb.pow 3) (fun x => pow_ne_zero 3 (hpos x).ne')).neg
  let a : Fin 6 → ManifoldSmoothFunctions E M := fun i =>
    if i = 1 then ⟨fun x => (-(Λ * s x / b x ^ 3) : ℝ), Complex.ofRealCLM.contMDiff.comp ha1⟩
    else if i = 5 then ⟨fun _ => (Λ : ℂ), contMDiff_const⟩
    else 0
  have he' (x : M) : complexLaplaceBeltrami g' (fun x => (u x : ℂ)) x =
      ∑ i, a i x * (u x : ℂ) ^ i.val := by
    rw [complexLaplaceBeltrami_ofReal]
    change (laplaceBeltrami (conformalMetric g b hb hpos) u x : ℂ) = _
    rw [conformalMetric_laplacian_three hd, he]
    simp only [a, Fin.sum_univ_succ]
    norm_num [Fin.ext_iff, ContMDiffMap.coe_zero, ContMDiffMap.coeFn_mk]
    have hn : (b x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos x).ne'
    field_simp
    ring
  have hu' := B.represented_semilinear_solution_smooth a
    (Complex.ofRealCLM.contMDiff.comp hu) he' v' hv'
  have hr := Complex.reCLM.contMDiff.comp hu'
  exact hr
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
