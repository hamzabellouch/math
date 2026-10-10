import OAI.Combinatorics.Ryser.LineCover.Definitions
import OAI.Combinatorics.Ryser.LineCover.ProjectiveLift
import OAI.Combinatorics.Ryser.Incidence.Uniform

namespace OAI

open scoped BigOperators Classical
noncomputable section

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F]

theorem heavy_incidence_sum_le
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T : ℝ)
    (hheavy : ((heavyPoints Incidence X L T).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent))
    (hL : L.card ≤ Fintype.card F) :
    (∑ x ∈ heavyPoints Incidence X L T, (multiplicity Incidence L x : ℝ)) ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - Incidence.savingExponent) := by
  have hqone : 1 ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := F)))
  have hqpow : (Fintype.card F : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hqone
        (show (1 : ℝ) ≤ 1 + Incidence.savingExponent by
          linarith [Incidence.savingExponent_pos]))
  have hbound := Incidence.uniform_incidence_bound F hq hsub
    (projectivePointsOf (heavyPoints Incidence X L T)) (projectiveLinesOf L)
    (by simpa only [card_projectivePointsOf] using hheavy)
    (by
      rw [card_projectiveLinesOf]
      exact (show (L.card : ℝ) ≤ (Fintype.card F : ℝ) by
        exact_mod_cast hL).trans hqpow)
  rw [incidenceCount_projective_lifts, Nat.cast_sum] at hbound
  exact hbound

theorem orderedPairMass_le_of_uniform_incidence
    (hq : Incidence.incidenceThreshold ≤ Fintype.card F)
    (hsub : Incidence.SmallProperSubfields F)
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T R : ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hheavy : ((heavyPoints Incidence X L T).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 + Incidence.savingExponent))
    (hL : L.card ≤ Fintype.card F)
    (hpencil : ∀ p : ProjectivePoint F, ((coverPencil L p).card : ℝ) ≤ R) :
    (orderedPairMass Incidence X L : ℝ) ≤
      T * (overlapExcess Incidence X L : ℝ) +
        R * (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - Incidence.savingExponent) := by
  have hpoint : ∀ x ∈ X, (multiplicity Incidence L x : ℝ) ≤ R := by
    intro x _
    rw [multiplicity_eq_finite_pencil]
    simpa only [coverPencil] using hpencil (Sum.inl x)
  exact (orderedPairMass_le_light_add_heavy Incidence X L T R hT hpoint).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (heavy_incidence_sum_le hq hsub X L T hheavy hL) hR))

theorem heavyPoints_card_le_of_excess
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (T B : ℝ)
    (hT : 1 < T) (hE : (overlapExcess Incidence X L : ℝ) ≤ B) :
    ((heavyPoints Incidence X L T).card : ℝ) ≤ B / (T - 1) := let _ := instFintypeF; by
  apply (le_div_iff₀ (sub_pos.mpr hT)).2
  exact (heavyPoints_card_mul_le_excess Incidence X L T hT).trans hE

end RyserCoveringCounterexample.LineCover

end

end OAI
