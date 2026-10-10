import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.ExcessSourcePlaneMoments
import OAI.Analysis.RieszRectifiability.Limits.DyadicFullPlanarMeasureLimit
import OAI.Analysis.RieszRectifiability.Limits.BilateralFlatLimit

namespace OAI

/-!
# Bilateral flatness along a subsequence

Vanishing dyadic excess and scalar oscillation yield a planar weak limit after
shifting and extracting a subsequence. Lower mass bounds then turn this planar
limit into convergence of the original measures' bilateral beta numbers at every
fixed positive radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_original_bilateral_sequence_limit {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (hδpos : ∀ j, 0 < δ j) (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j))
    (b : ℝ) (hb : 1 < b) (hsmall : Tendsto (fun j => δ j * b ^ T j) atTop (𝓝 0))
    (hexcess : ∀ j l, l ≤ T j →
      squaredExcess (p + 1) (μ j) 0 ((2 : ℝ) ^ l) ≤ (δ j * b ^ l) ^ 2)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 < r →
      Tendsto (fun j => bilateralBeta (p + 1) (μ (ρ j)) 0 r) atTop (𝓝 0) := by
  obtain ⟨J, M, _, S, hS, hmoment⟩ := exists_shifted_fixed_plane_source_moments hnd
    μ C G hC hg (fun j r hr => hlower j 0 (hzero j) r hr)
    δ hδpos T horizon b hb hsmall hexcess
  have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
  have hdiam := support_diameters_grow_of_admissible_dyadic_horizon μ T hT horizon
  have hv : Tendsto (fun j => δ (j + J) ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using! (hδ.comp hshift).pow 3
  obtain ⟨ρ, hρ, ν, _, _, _, Llim, hfinite, _, hweak, _, _, hsupport, _⟩ :=
    exists_dyadic_full_planar_measure_limit (fun j => μ (j + J)) C G hC
      (fun j => hg (j + J)) (fun j => hlower (j + J))
      (fun r hr => hshift.eventually (hdiam r hr)) (fun j => hzero (j + J)) S hS
      (fun j => δ (j + J)) (fun j => T (j + J)) (hδ.comp hshift) (hT.comp hshift)
      M b hmoment (fun j => A (j + J)) (fun j => δ (j + J) ^ 3)
      (hA.comp hshift) hv (fun j => hosc (j + J))
  let : IsFiniteMeasureOnCompacts ν := hfinite
  refine ⟨fun j => ρ j + J, (fun _ _ hij => Nat.add_lt_add_right (hρ hij) J), ?_⟩
  intro r hr
  exact compactTestConvergence_bilateralBeta_tendsto_zero (p + 1) (fun j => μ (ρ j + J)) ν
    hweak C hC (fun j => hlower (ρ j + J))
    (fun s hs => hρ.tendsto_atTop.eventually (hshift.eventually (hdiam s hs)))
    Llim.toLinearMap.range.toAffineSubspace (isAffineNPlane_isometric_range Llim) hsupport 0 r hr

end

end RieszRectifiability

end OAI
