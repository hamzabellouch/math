import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.AdmissibleDyadicHorizon
import OAI.Analysis.RieszRectifiability.Flatness.FixedPlaneDyadicMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_shifted_fixed_plane_source_moments {n d : ℕ} (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball 0 r))
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (T : ℕ → ℕ)
    (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j))
    (b : ℝ) (hb : 1 < b) (hsmall : Tendsto (fun j => δ j * b ^ T j) atTop (𝓝 0))
    (hexcess : ∀ j l, l ≤ T j → squaredExcess n (μ j) 0 ((2 : ℝ) ^ l) ≤ (δ j * b ^ l) ^ 2) :
    ∃ J : ℕ, ∃ M : ℝ, 0 < M ∧ ∃ S : ℕ → AffineSubspace ℝ (Ambient d),
      (∀ j, IsAffineNPlane n (S j)) ∧ ∀ j l, l ≤ T (j + J) →
        (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2
          ∂μ (j + J)) ≤ M * (δ (j + J) * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2) := by
  obtain ⟨M, κ, hM, hκ, hfit⟩ := exists_uniform_fixed_plane_dyadic_moments hnd G C⁻¹ b
    (hg 0).1 (inv_pos.mpr hC) hb
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hsmall.eventually (gt_mem_nhds hκ))
  have hfits (j : ℕ) := hfit (μ (j + J)) inferInstance (hg (j + J)) (T (j + J)) (δ (j + J))
    (hδ (j + J)) (hJ (j + J) (by omega)).le
    (fun l hl => dyadic_lower_real_mass_of_admissible_horizon n C G (μ (j + J)) hC
      (hg (j + J)) (hlower (j + J)) (T (j + J)) (horizon (j + J)) l hl)
    (hexcess (j + J))
  choose P hP _hfit hfixed using hfits
  exact ⟨J, M, hM, (fun j => P j 0), (fun j => hP j 0), hfixed⟩

end

end RieszRectifiability

end OAI
