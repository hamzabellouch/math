import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SourceRadialCutoffMass
import OAI.Analysis.RieszRectifiability.Kernel.SourceNormalizedMoments
import OAI.Analysis.RieszRectifiability.Kernel.OscillationEnergy
import OAI.Analysis.RieszRectifiability.Kernel.DyadicSourceTails

namespace OAI

/-!
# Uniform energy of normalized source heights

Dyadic second-moment bounds and vanishing oscillation control the fractional pair
energy of normalized affine heights on each fixed ball. Eventual estimates extend
to a nonnegative bound for the whole sequence, with integrability retained.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_normalized_energy_on_ball {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (a : Ambient d) (hC : 0 < C)
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball a r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (W : ℝ) (hW : ∀ j, |u j a| ≤ W)
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (δ j ^ 3))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ j,
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
        (((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
          ∂((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ≤ E := by
  let : ∀ j, IsFiniteMeasureOnCompacts (μ j) := fun j => (hg j).finite_on_compacts
  let H := r + 1
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (max 1 (2 * H)) (by norm_num : (1 : ℝ) < 2)
  let R : ℝ := 2 ^ q
  have hR : 1 ≤ R := (le_max_left _ _).trans hq.le
  have hHR : 2 * H ≤ R := (le_max_right _ _).trans hq.le
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hrR : r ≤ R := by dsimp [H] at hHR; linarith
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let c : ℝ := r ^ (p + 1) / C
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨M, hM, hmass, hsecond⟩ := source_unnormalized_second_moments_on_ball
    (p + 1) G μ hg u K hu a δ hδ N hN D b hsource R hRpos
  have huL2 (l j : ℕ) : MemLp (u j) 2 ((μ j).restrict (ball a ((2 : ℝ) ^ l))) :=
    lipschitz_height_memLp_on_ball (p + 1) G (μ j) (hg j) (u j) K (hu j)
      a ((2 : ℝ) ^ l) (by positivity)
  obtain ⟨B, hGB, hshell⟩ := controlled_shell_moments_from_dyadic_balls
    (p + 1) μ a u δ N D b (G * 2 ^ (p + 1)) huL2 hsource q
  have hshift := (dyadic_shifted_last_error_tendsto q N δ hN hlast).2
  have hcut := source_radial_cutoff_mass_eventually (p + 1) C G μ hg a hC
    hlower hdiam r R hr hrR
  let χ := radialUnitCutoff a r
  have hχbound (x : Ambient d) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (radialUnitCutoff_bounds a r x).1]
    exact (radialUnitCutoff_bounds a r x).2
  let E := uncenteredEnergyCoefficient p G B M c H R b W
    ((centeredHeightTestConstant M c H W K 1 : ℝ) + 1) K 1
  have hE : ∀ᶠ j in atTop,
      (∫ v : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u j x / δ j) v.1 v.2
          ∂((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ≤ E := by
    filter_upwards [hcut, hδlim.eventually (gt_mem_nhds zero_lt_one),
      hA.eventually (eventually_gt_atTop H), hshift.eventually (gt_mem_nhds zero_lt_one)]
      with j hjcut hjδ hjA hjlast
    have hlastj : (R * 2 ^ (N j - (q + 1)))⁻¹ ≤ δ j := by
      exact ((div_lt_iff₀ (hδ j)).mp hjlast).le.trans_eq (one_mul _)
    have h := inner_energy_bound_from_oscillation p G B (μ j) (hg j) hGB (z j) (hz j)
      (u j) χ K 1 (hu j) (radialUnitCutoff_lipschitz a r) (hdiff j) hχbound
      a r H R (A j) hH hR hHR hrR hjA
      (fun x hx => radialUnitCutoff_support_bound a r x hx)
      (fun x hx => radialUnitCutoff_eq_one a r x hx.le)
      M c (δ j) b W hM hc (hδ j) hjδ.le hb1 hb2 (hW j)
      (N j - (q + 1)) hlastj hmass hjcut (hsecond j) (hshell j) (hosc j)
    exact h.2.2
  obtain ⟨E', hE', hb⟩ := nonnegative_uniform_bound_of_eventually_le _ E hE
  exact ⟨E', hE', fun j =>
    ⟨normalized_lipschitz_energy_integrable_on_ball p G (μ j) (hg j) (u j) K (hu j)
      a r (δ j) hr, hb j⟩⟩

end

end RieszRectifiability

end OAI
