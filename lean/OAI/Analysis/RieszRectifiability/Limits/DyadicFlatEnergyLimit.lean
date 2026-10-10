import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.DyadicFlatMeasureLimit
import OAI.Analysis.RieszRectifiability.Packing.NormalFrameSourceEnergy

namespace OAI

/-!
# Dyadic flat limits with normalized height energy

The flat-measure subsequence construction is augmented with uniform local square
and fractional-energy bounds for every normalized normal coordinate. The ball
estimates also restrict to bounded projection regions, while the same subsequence
retains the convergent plane frames, constant positive planar density, and scalar
reflectionlessness of the limit measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_flat_measure_limit_with_energy {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hδpos : ∀ j, 0 < δ j) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        GlobalUpperGrowth (p + 1) (G * 2 ^ (p + 1)) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤ ν (ball x r)) ∧
        ν.support = (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient (p + 1) → ℝ, Measurable f ∧
          (∀ x, intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) ≤ f x ∧
            f x ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) ∧
          ((volume : Measure (Ambient (p + 1))).withDensity
            (fun x => ENNReal.ofReal (f x))).map Llim = ν ∧
          ∃ q : ℝ, 0 < q ∧
            (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) : ℝ) ≤ q ∧
            q ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1)) ∧
            (∀ᵐ x ∂volume, f x = q) ∧
            ν = ENNReal.ofReal q • (volume : Measure (Ambient (p + 1))).map Llim) ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
            normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) ∧
        (∀ i : Fin (d - (p + 1)), ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 r)) ∧
          (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B ∧
          Integrable (fun v : Ambient d × Ambient d =>
            fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
            (((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ∧
          (∫ v : Ambient d × Ambient d,
            fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
              ∂((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ≤ E) ∧
        (∀ i : Fin (d - (p + 1)), ∀ π : Ambient d → Fin (p + 1) → ℝ, ∀ K : ℝ≥0,
          ∃ B E : ℕ → ℝ, ∀ H, 0 ≤ B H ∧ 0 ≤ E H ∧ ∀ j,
            MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
              ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) ∧
            (∫ x in boundedProjectionRegion π 0 K H,
              (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B H ∧
            Integrable (fun v : Ambient d × Ambient d =>
              fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
              (((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
                ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ∧
            (∫ v : Ambient d × Ambient d,
              fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
                ∂((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
                  ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ≤ E H) ∧
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  have hv : Tendsto (fun j => δ j ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using! hδ.pow 3
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist,
    hmem, hsource, hreflect⟩ :=
    exists_dyadic_flat_measure_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A (fun j => δ j ^ 3) hA hv hosc D hB
  have hdata := normal_frame_source_data_on_ball p C G (fun j => μ (ρ j))
    (fun j => hg (ρ j)) hC (fun j r hr => hlower (ρ j) 0 (hzero (ρ j)) r hr)
    (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr)) a ha N
    (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => hδpos (ρ j))
    (hδ.comp hρ.tendsto_atTop) (hA.comp hρ.tendsto_atTop) (fun j => hosc (ρ j))
    (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop) M b hb1 hb2
    (hlast.comp hρ.tendsto_atTop) hsource
  refine ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource,
    hdata, ?_, hreflect⟩
  intro i π K
  exact normalized_region_data_of_ball_data (p + 1) (fun j => μ (ρ j))
    (fun j x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 0 (hdata i) π K

end

end RieszRectifiability

end OAI
