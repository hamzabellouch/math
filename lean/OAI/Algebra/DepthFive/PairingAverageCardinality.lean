import OAI.Algebra.DepthFive.LocalMomentPairing

namespace OAI

/-! Multiplying a genuine normalized source average introduces exactly one
source-cardinality factor, including when the source is empty. -/
noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing
open Pairings

theorem sum_sources_local_moments_le_of_average {ι γ : Type*} [Fintype ι]
    [Fintype γ] [DecidableEq γ] {L : ℕ}
    (side : Fin (L + 1) → Bool) {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (endpoint : γ)
    (C : ι → (Fin L → Labels γ) → ℝ)
    (haverage : ∀ x, Compatible endpoint x →
      (∑ i, C i x) / (Fintype.card ι : ℝ) ≤
        ∏ t, LocalMoments.localGeometricMass (side t) (if side t then A else B)
          (layerLabels endpoint x t).p (layerLabels endpoint x t).q
          (layerLabels endpoint x t).r) :
    (∑ i, ∑ x : {x : Fin L → Labels γ // Compatible endpoint x}, C i x.1) ≤
      (Fintype.card ι : ℝ) * pathMean side A B ^ 2 *
        ∑ τ : Fin (L + 1) → Kind, ∑ x : RelaxedPaths γ endpoint τ,
          pathWeight side (A / (A + 1)) (B / (B + 1)) endpoint τ x.1 := by
  classical
  apply sum_sources_local_moments_le side hA hB (by positivity) endpoint C
  intro x hx
  by_cases hcard : Fintype.card ι = 0
  · let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    simp
  · have hpos : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    simpa only [mul_comm] using (div_le_iff₀ hpos).mp (haverage x hx)

end Problem335.MomentPairing

end

end OAI
