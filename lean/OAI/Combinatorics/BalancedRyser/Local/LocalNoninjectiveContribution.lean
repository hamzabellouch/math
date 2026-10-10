import OAI.Combinatorics.BalancedRyser.Local.AlignmentNormalization
import OAI.Combinatorics.BalancedRyser.Local.LocalDirectionAssignments
import OAI.Combinatorics.BalancedRyser.Local.LocalKernel

namespace OAI

namespace Balanced.Local

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem joint_alignment_probability_le {b κ : ℕ} (P : EqualityPattern b κ)
    (hκ : κ ≤ 2) (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (E : MergedPairs F → Prop) :
    offsetProbability (fun M => Aligned P a bits p M ∧ E M) ≤
      1 / (Fintype.card F : ℝ) ^ (4 * b) := by
  calc
    _ ≤ offsetProbability (Aligned P a bits p) :=
      KernelBridge.offsetProbability_mono (fun _ h => h.1)
    _ = _ := alignment_probability P hκ a ha bits p

theorem sum_noninjective_joint_le {b : ℕ} (hb : 1 ≤ b)
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b 2 → MergedPairs F → Prop) :
    (∑ a : DirectionAssignment F b 2,
      if Eligible P a ∧ ¬ AllTokensDistinct a then
        offsetProbability (fun M => Aligned P a bits p M ∧ E a M) else 0) ≤
      (b : ℝ) * (4 * b - 2 : ℕ) * (Fintype.card F + 1 : ℕ) ^ (5 * b - 3) /
        (Fintype.card F : ℝ) ^ (4 * b) := by
  let S := (Finset.univ : Finset (DirectionAssignment F b 2)).filter
    (fun a => Eligible P a ∧ ¬ AllTokensDistinct a)
  have hsum : (∑ a ∈ S,
      offsetProbability (fun M => Aligned P a bits p M ∧ E a M)) ≤
      (S.card : ℝ) * (1 / (Fintype.card F : ℝ) ^ (4 * b)) := by
    calc
      _ ≤ ∑ _a ∈ S, (1 / (Fintype.card F : ℝ) ^ (4 * b)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact joint_alignment_probability_le P (by omega) a
          (Finset.mem_filter.mp ha).2.1 bits p (E a)
      _ = _ := by simp
  have hcard : (S.card : ℝ) ≤
      (b : ℝ) * (4 * b - 2 : ℕ) * (Fintype.card F + 1 : ℕ) ^ (5 * b - 3) := by
    exact_mod_cast card_eligible_not_allDistinct_two_le (F := F) hb P
  calc
    _ = ∑ a ∈ S, offsetProbability (fun M => Aligned P a bits p M ∧ E a M) := by
      simp only [S, Finset.sum_filter]
    _ ≤ (S.card : ℝ) * (1 / (Fintype.card F : ℝ) ^ (4 * b)) := hsum
    _ ≤ ((b : ℝ) * (4 * b - 2 : ℕ) * (Fintype.card F + 1 : ℕ) ^ (5 * b - 3)) *
        (1 / (Fintype.card F : ℝ) ^ (4 * b)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

theorem noninjective_coefficient_le {b : ℕ} (hb : 1 ≤ b)
    {q : ℝ} (hq : 0 < q) :
    (b : ℝ) * (4 * b - 2 : ℕ) * (q + 1) ^ (5 * b - 3) / q ^ (4 * b) ≤
      (q + 1) ^ (5 * b - 2) / q ^ (4 * b) * (4 * (b : ℝ) ^ 3 / q) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hsub : ((4 * b - 2 : ℕ) : ℝ) ≤ 4 * (b : ℝ) := by
    exact_mod_cast (Nat.sub_le (4 * b) 2)
  have hbnonneg : (0 : ℝ) ≤ b := by positivity
  have hcoef : (b : ℝ) * (4 * b - 2 : ℕ) ≤ 4 * (b : ℝ) ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_left hsub hbnonneg
    have h₂ : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 3 := by
      nlinarith [sq_nonneg (b : ℝ)]
    nlinarith
  have hexp : 5 * b - 2 = (5 * b - 3) + 1 := by omega
  have hbase : (b : ℝ) * (4 * b - 2 : ℕ) * q ≤
      4 * (b : ℝ) ^ 3 * (q + 1) := by
    have h := mul_le_mul_of_nonneg_right hcoef hq.le
    nlinarith [pow_nonneg hbnonneg 3]
  have hbase' : (b : ℝ) * (4 * b - 2 : ℕ) ≤
      4 * (b : ℝ) ^ 3 * (q + 1) / q := (le_div_iff₀ hq).mpr hbase
  calc
    _ = ((q + 1) ^ (5 * b - 3) / q ^ (4 * b)) *
        ((b : ℝ) * (4 * b - 2 : ℕ)) := by ring
    _ ≤ ((q + 1) ^ (5 * b - 3) / q ^ (4 * b)) *
        (4 * (b : ℝ) ^ 3 * (q + 1) / q) :=
      mul_le_mul_of_nonneg_left hbase' (by positivity)
    _ = _ := by rw [hexp, pow_succ]; ring

theorem sum_noninjective_badCover_le {b : ℕ} (hb : 1 ≤ b)
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) :
    (∑ a : DirectionAssignment F b 2,
      if Eligible P a ∧ ¬ AllTokensDistinct a then
        offsetProbability (fun M =>
          Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) ≤
      ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
        (Fintype.card F : ℝ) ^ (4 * b) * (4 * (b : ℝ) ^ 3 / Fintype.card F) := by
  apply (sum_noninjective_joint_le hb P bits p
    (fun a => AdmissibleBadCover P a bits p)).trans
  simpa only [Nat.cast_add, Nat.cast_one] using
    noninjective_coefficient_le hb (q := (Fintype.card F : ℝ)) (by positivity)

end
end Balanced.Local

end OAI
