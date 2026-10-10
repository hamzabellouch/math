import OAI.Combinatorics.BalancedRyser.Local.LocalPrescriptionCounting

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

theorem alignment_and_badCover_probability (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) :
    offsetProbability (fun M => Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) =
      offsetProbability (AdmissibleBadCover P a bits p) := by
  congr 1
  funext M
  apply propext
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

theorem badCover_probability_le_of_conditioned (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) (t : ℝ)
    (hnorm : offsetProbability (Aligned P a bits p) =
      1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hcond : conditionedOffsetProbability (Aligned P a bits p)
      (AdmissibleBadCover P a bits p) ≤ t) :
    offsetProbability (AdmissibleBadCover P a bits p) ≤
      1 / (Fintype.card F : ℝ) ^ (4 * b) * t := by
  unfold conditionedOffsetProbability at hcond
  rw [alignment_and_badCover_probability, hnorm] at hcond
  have hp : (0 : ℝ) < 1 / (Fintype.card F : ℝ) ^ (4 * b) := by positivity
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hcond

omit [Field F] [DecidableEq F] in

theorem card_directionAssignment (hk : κ ≤ 4 * b) :
    Fintype.card (DirectionAssignment F b κ) =
      (Fintype.card F + 1) ^ (5 * b - κ) := by
  simp only [DirectionAssignment, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Direction, Fintype.card_option]
  rw [← pow_add]
  congr 1
  omega

theorem directionBadCoverMass_le_of_conditioned
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (hk : κ ≤ 4 * b) (t : ℝ) (ht : 0 ≤ t)
    (hnorm : ∀ a : DirectionAssignment F b κ, Eligible P a →
      offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hcond : ∀ a : DirectionAssignment F b κ, Eligible P a →
      conditionedOffsetProbability (Aligned P a bits p)
        (AdmissibleBadCover P a bits p) ≤ t) :
    directionBadCoverMass P bits p ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - κ) /
        (Fintype.card F : ℝ) ^ (4 * b) * t := by
  unfold directionBadCoverMass
  simp only [alignment_and_badCover_probability]
  calc
    _ ≤ ∑ _a : DirectionAssignment F b κ,
        1 / (Fintype.card F : ℝ) ^ (4 * b) * t := by
      apply Finset.sum_le_sum
      intro a _
      by_cases he : Eligible P a
      · rw [ite_eq_left he]
        exact badCover_probability_le_of_conditioned P a bits p t (hnorm a he) (hcond a he)
      · rw [ite_eq_right he]
        positivity
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_directionAssignment hk]
      push_cast
      ring

theorem bad_pencil_probability_le_of_conditioned
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : KernelConditions Q w K) (p : Point F) (hb : 2 ≤ b) (hk : κ ≤ 2)
    (t : ℝ) (ht : 0 ≤ t)
    (hnorm : ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
      ∀ bits : Bits b, offsetProbability (Aligned P a bits p) =
        1 / (Fintype.card F : ℝ) ^ (4 * b))
    (hcond : ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
      ∀ bits : Bits b, conditionedOffsetProbability (Aligned P a bits p)
        (AdmissibleBadCover P a bits p) ≤ t) :
    selectedProbability w (fun C => C.splitMultiplicity p = b ∧
      reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
      (4 * (b : ℝ)) ^ 4 * (1024 * K) ^ b / (b.factorial : ℝ) *
        (t / (Fintype.card F : ℝ) ^ κ) := by
  apply bad_pencil_probability_le_common_factor Q w K hK0 hK p hb hk t ht
  intro P bits
  exact directionBadCoverMass_le_of_conditioned P bits p (by omega) t ht
    (fun a ha => hnorm P a ha bits) (fun a ha => hcond P a ha bits)

end
end Balanced.Local

end OAI
