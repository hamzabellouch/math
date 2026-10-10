import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.DyadicFullPlanarMeasureLimit
import OAI.Analysis.RieszRectifiability.Foundations.SourceDensityConstant

namespace OAI

/-!
# Flat limits from dyadic moment bounds

Dyadic plane-approximation bounds and vanishing scalar oscillation produce a planar weak limit.
Uniform hard-truncation bounds then force its density to be a positive constant. The conclusion
retains the limiting coordinates, quantitative density bounds, and normal-coordinate moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_flat_measure_limit {p d : ℕ}
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
    (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (v j))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j)) :
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
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, ⟨f, hf, hfb, hpush⟩, ha, hLlim, hcenter, hL, horth, hsplit, hdist,
    hmem, hsource, hreflect⟩ :=
    exists_dyadic_full_planar_measure_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A v hA hv hosc
  let : IsFiniteMeasureOnCompacts ν := hfinite
  have hC' : 0 < C * 4 ^ (p + 1) := mul_pos hC (pow_pos (by norm_num) _)
  have hpos : 0 < (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) : ℝ) :=
    NNReal.coe_pos.mpr (intrinsicLowerDensityBound_pos (p + 1) _ hC')
  have habs (x : Ambient (p + 1)) :
      |f x| ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1)) := by
    rw [abs_of_nonneg (hpos.le.trans (hfb x).1)]
    exact (hfb x).2
  have hlm (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal ((C * 4 ^ (p + 1))⁻¹ * r ^ (p + 1)) ≤ ν (ball 0 r) := by
    simpa only [div_eq_mul_inv, mul_comm] using! hlowerν 0 horigin r hr
  obtain ⟨q, hcq, hqM, hq, hfq, hflat⟩ :=
    source_planar_density_ae_constant p G (G * 2 ^ (p + 1)) (fun j => μ (ρ j)) ν
      (fun j => hg (ρ j)) hgν hweak D (fun j => hB (ρ j)) Llim f hf
      (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1))) hpos (fun x => (hfb x).1)
      (intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) habs hpush
      (C * 4 ^ (p + 1))⁻¹ (inv_pos.mpr hC') hlm (hreflect 0)
  exact ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hsupport,
    horigin, ⟨f, hf, hfb, hpush, q, hq, hcq, hqM, hfq, hflat⟩,
    ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource, hreflect⟩

end

end RieszRectifiability

end OAI
