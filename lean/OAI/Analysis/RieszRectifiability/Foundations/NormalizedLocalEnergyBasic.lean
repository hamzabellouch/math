import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedEnergy

namespace OAI

/-!
# Local integrability of normalized Lipschitz energies

Growth bounds make normalized Lipschitz functions square-integrable on balls and
their fractional pair energies integrable on the corresponding product measure.
An auxiliary sequence bound absorbs finitely many exceptional scales into one nonnegative bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem normalized_lipschitz_memLp_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (u : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (r δ : ℝ) (hr : 0 < r) :
    MemLp (fun x => u x / δ) 2 (μ.restrict (ball a r)) := by
  have h := (lipschitz_height_memLp_on_ball n G μ hg u K hu a r hr).const_smul δ⁻¹
  change MemLp (fun x => δ⁻¹ * u x) 2 (μ.restrict (ball a r)) at h
  simpa only [div_eq_mul_inv, mul_comm] using! h

theorem normalized_lipschitz_energy_integrable_on_ball {d : ℕ} (p : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) G μ)
    (u : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (r δ : ℝ) (hr : 0 < r) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2)
      ((μ.restrict (ball a r)).prod (μ.restrict (ball a r))) := by
  let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) G μ hg a r hr
  have hK : ∀ᵐ q ∂(μ.restrict (ball a r)).prod (μ.restrict (ball a r)),
      |u q.1 - u q.2| ≤ (K : ℝ) * dist q.1 q.2 := by
    exact Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hu.dist_le_mul q.1 q.2
  have hE := fractionalEnergy_integrable_of_ae_lipschitz p G (μ.restrict (ball a r))
    (globalGrowth_restrict (p + 1) G μ hg (ball a r)) u hu.continuous.measurable K hK
    (2 * r) (by positivity) (ball_restriction_pair_diameter μ a r)
  simpa only [fractionalPairEnergy_div] using! hE.div_const (δ ^ 2)

theorem nonnegative_uniform_bound_of_eventually_le (f : ℕ → ℝ) (B : ℝ)
    (hB : ∀ᶠ j in atTop, f j ≤ B) : ∃ M : ℝ, 0 ≤ M ∧ ∀ j, f j ≤ M := by
  have h : IsBoundedUnder (· ≤ ·) atTop f := ⟨B, hB⟩
  obtain ⟨M, hM⟩ := h.bddAbove_range
  exact ⟨max 0 M, le_max_left _ _, fun j => (hM ⟨j, rfl⟩).trans (le_max_right _ _)⟩

end

end RieszRectifiability

end OAI
