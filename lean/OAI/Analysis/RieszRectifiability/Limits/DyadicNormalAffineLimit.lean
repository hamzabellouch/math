import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.DyadicFlatEnergyLimit
import OAI.Analysis.RieszRectifiability.Limits.NormalCommonAffineStrongLimit

namespace OAI

/-!
# Affine limits of dyadic normal heights

A flat-measure subsequence supplies positive planar density and convergent tangent
frames. A further common subsequence makes every normalized normal coordinate
converge strongly to an affine height on bounded projection regions, retaining
the frame decomposition and the weak measure limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_normal_affine_limit {p d : ℕ}
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
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d), ∃ t : ℝ, 0 < t ∧
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        ν = ENNReal.ofReal t • (volume : Measure (Ambient (p + 1))).map Llim ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        ∃ c : Fin (d - (p + 1)) → ℝ,
          ∃ B : Fin (d - (p + 1)) → Ambient (p + 1) →L[ℝ] ℝ, ∀ i H,
            Tendsto (fun j => ∫ x,
              (normalCoordinate (a j) (N j) i x / δ (ρ j) -
                ambientAffineHeight 0 Llim (c i) (B i) x) ^ 2
              ∂(μ (ρ j)).restrict
                (boundedProjectionRegion (affinePlaneCoordinates 0 Llim) 0
                  ((Fintype.card (Fin (p + 1)) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) H))
              atTop (𝓝 0) := by
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, _, _, _, _,
    hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, _, hsource, _, _, _⟩ :=
    exists_dyadic_flat_measure_limit_with_energy μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A hA hosc D hB hδpos hb1 hb2 hlast
  obtain ⟨f, _, _, _, t, ht, _, _, _, hν⟩ := hdensity
  have hplane : coordinatePlaneMeasure (affinePlaneSection 0 Llim) =
      (volume : Measure (Ambient (p + 1))).map Llim := by
    simpa only [zero_add] using! coordinatePlaneMeasure_affine_eq_map (0 : Ambient d) Llim
  have hν' : ν = ENNReal.ofReal t • coordinatePlaneMeasure (affinePlaneSection 0 Llim) := by
    rw [hplane]
    exact hν
  obtain ⟨τ, hτ, c, B, hstrong⟩ := exists_normal_common_affine_strong_limit
    (affinePlaneSection 0 Llim) (affinePlaneCoordinates 0 Llim)
    ((Fintype.card (Fin (p + 1)) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
    ‖Llim.toContinuousLinearMap.adjoint‖₊ (affinePlaneSection_lipschitz 0 Llim)
    (affinePlaneCoordinates_lipschitz 0 Llim) (affinePlaneCoordinates_leftInverse 0 Llim)
    Llim rfl (fun j => μ (ρ j)) ν hweak t ht hν' C G hC
    (fun j => hg (ρ j)) (fun j => hlower (ρ j))
    (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr)) (fun j => hzero (ρ j))
    a ha N (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => hδpos (ρ j))
    (hδ.comp hρ.tendsto_atTop) (hA.comp hρ.tendsto_atTop) (fun j => hosc (ρ j))
    (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop) M b hb1 hb2
    (hlast.comp hρ.tendsto_atTop) hsource
  refine ⟨ρ ∘ τ, hρ.comp hτ, ν, t, ht, a ∘ τ, L ∘ τ, N ∘ τ, Llim, hfinite, hne,
    ?_, hν, ha.comp hτ.tendsto_atTop, hLlim.comp hτ.tendsto_atTop,
    (fun j => hcenter (τ j)), (fun j => hL (τ j)),
    (fun j => horth (τ j)), (fun j => hsplit (τ j)), (fun j => hdist (τ j)), c, B, hstrong⟩
  intro g
  exact (hweak g).comp hτ.tendsto_atTop

end

end RieszRectifiability

end OAI
