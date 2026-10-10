import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.DyadicReflectionlessMeasureLimit
import OAI.Analysis.RieszRectifiability.Rigidity.PlanarReflectionlessSupport
import OAI.Analysis.RieszRectifiability.Foundations.TwoSidedIntrinsicDensity

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_full_planar_measure_limit {p d : ℕ}
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
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (v j)) :
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
            (fun x => ENNReal.ofReal (f x))).map Llim = ν) ∧
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
    horigin, _hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, hmem, hsource, hreflect⟩ :=
    exists_dyadic_reflectionless_measure_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A v hA hv hosc
  have hC' : 0 < C * 4 ^ (p + 1) := mul_pos hC (pow_pos (by norm_num) _)
  have hfull := planar_full_support_of_reflectionless Llim ν hne hsupport
    (C * 4 ^ (p + 1)) (G * 2 ^ (p + 1)) hC' hgν hlowerν (fun c _ => hreflect c)
  have hlowerμ := planarPullbackMeasure_lower Llim ν hsupport (C * 4 ^ (p + 1)) hlowerν
  have hlowerAll : ∀ x : Ambient (p + 1), ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤
        planarPullbackMeasure Llim ν (ball x r) := by
    intro x r hr
    apply hlowerμ x _ r hr
    rw [hfull.1]
    exact mem_univ x
  obtain ⟨f, hm, hb, heq⟩ := exists_two_sided_intrinsic_density (p + 1)
    (C * 4 ^ (p + 1)) (G * 2 ^ (p + 1)) (planarPullbackMeasure Llim ν) hC'
    (planarPullbackMeasure_growth Llim ν hsupport (G * 2 ^ (p + 1)) hgν) hlowerAll
  have hpush : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map Llim = ν := by
    rw [heq]
    exact planarPullbackMeasure_recover Llim ν hsupport
  exact ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, hgν, hlowerν, hfull.2,
    horigin, ⟨f, hm, hb, hpush⟩, ha, hLlim, hcenter, hL, horth, hsplit, hdist,
    hmem, hsource, hreflect⟩

end

end RieszRectifiability

end OAI
