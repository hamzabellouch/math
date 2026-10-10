import OAI.Combinatorics.BalancedRyser.Probability.FreshTupleWitness

namespace OAI

namespace Balanced.FreshTupleWitness

noncomputable section
open scoped Classical BigOperators
open TupleAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def freshOrientedEvent (g : Direction F) (i j : Fin 4)
    (a : RootPrescription g) (d : Direction F) (σ : Bool)
    (M : MergedPairs F) : Prop :=
  (∀ k, a.tuple.generator k ≠ d) ∧
  ((∃ c, ∀ k, OnLine (tuplePoint M a.tuple k) (g,c)) ∧
    Function.Injective (tuplePoint M a.tuple)) ∧
  OnLine (tuplePoint M a.tuple i) (constituent M d σ) ∧
  OnLine (tuplePoint M a.tuple j) (constituent M d (!σ))

theorem freshOrientedEvent_probability_le (g : Direction F) (i j : Fin 4)
    (a : RootPrescription g) (d : Direction F) (σ : Bool) :
    offsetEventProbability {M | freshOrientedEvent g i j a d σ M} ≤
      1 / (Fintype.card F : ℝ)^5 := by
  by_cases hd : ∀ k, a.tuple.generator k ≠ d
  · simpa [freshOrientedEvent, hd] using
      successful_oriented_pair_probability_le a.tuple a.injective g d hd i j σ
  · simp [freshOrientedEvent, hd, offsetEventProbability]

theorem sum_freshOrientedEvent_probability_le (g : Direction F) (i j : Fin 4) :
    (∑ a : RootPrescription g, ∑ d : Direction F, ∑ σ : Bool,
      offsetEventProbability {M | freshOrientedEvent g i j a d σ M}) ≤ 64 := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hdesc : ((Fintype.card F).descFactorial 4 : ℝ) ≤
      (Fintype.card F : ℝ)^4 := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card F) 4
  calc
    _ ≤ ∑ _a : RootPrescription g, ∑ _d : Direction F, ∑ _σ : Bool,
        (1 / (Fintype.card F : ℝ)^5) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro σ _
      exact freshOrientedEvent_probability_le g i j a d σ
    _ = 32 * ((Fintype.card F).descFactorial 4 : ℝ) *
        ((Fintype.card F : ℝ) + 1) / (Fintype.card F : ℝ)^5 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_bool, card_rootPrescription, Direction, Fintype.card_option,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ 32 * (Fintype.card F : ℝ)^4 *
        ((Fintype.card F : ℝ) + 1) / (Fintype.card F : ℝ)^5 := by
      gcongr
    _ ≤ 64 := by
      apply (div_le_iff₀ (by positivity : 0 < (Fintype.card F : ℝ)^5)).mpr
      nlinarith [mul_nonneg (pow_nonneg hq.le 4) (sub_nonneg.mpr hq1)]

end
end Balanced.FreshTupleWitness

end OAI
