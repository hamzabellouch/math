import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowth
import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyTreeSumLocal
import OAI.NumberTheory.Ostmann.Characters.FrequencyTreeSum

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.PairedFrequencyTreeSum
open Characters

def factor (C ε : ℝ) (_p : List Bool) (s v w : ℤ × ℤ) : ℝ :=
  C * (modulus s v w : ℝ) ^ (ε - 1)

def nodeBudget (C D ε δ : ℝ) (V : List Bool → ℕ) (p : List Bool) : ℝ :=
  4 * C * D ^ 2 * (V (false :: p) : ℝ) ^ δ * (V (true :: p) : ℝ) ^ δ *
    (V p : ℝ) ^ (2 * ε) * (1 + Real.log (V p)) ^ 3

theorem total_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ C ε : ℝ, 0 ≤ C → 0 ≤ ε →
      ∀ S : List Bool → Finset (ℤ × ℤ), ∀ V : List Bool → ℕ,
      (∀ p, 1 ≤ V p) →
      (∀ p s, s ∈ S p → (s.1 ≠ 0 ∧ s.1.natAbs ≤ V p) ∧
        (s.2 ≠ 0 ∧ s.2.natAbs ≤ V p)) → ∀ k p,
      FrequencyTreeSum.total S (factor C ε) k p ≤
        FrequencyTreeSum.budget S (nodeBudget C D ε δ V) k p := by
  obtain ⟨D,hD,hτ⟩ := divisors_card_le_rpow δ hδ
  refine ⟨D,hD,?_⟩
  intro C ε hC hε S V hV hS k p
  apply FrequencyTreeSum.total_le_budget
  · intro p s v w
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p
    have hl : 0 ≤ Real.log (V p) := Real.log_nonneg (by exact_mod_cast hV p)
    dsimp [nodeBudget]
    positivity
  · intro p v hv w hw
    have hvg : 0 < v.1.natAbs.gcd w.1.natAbs :=
      Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (hS _ _ hv).1.1)
    have hwg : 0 < v.2.natAbs.gcd w.2.natAbs :=
      Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr (hS _ _ hw).2.1)
    have hvl : v.1.natAbs.gcd w.1.natAbs ≤ V (false :: p) :=
      (Nat.gcd_le_left _ (Int.natAbs_pos.mpr (hS _ _ hv).1.1)).trans (hS _ _ hv).1.2
    have hwr : v.2.natAbs.gcd w.2.natAbs ≤ V (true :: p) :=
      (Nat.gcd_le_right _ (Int.natAbs_pos.mpr (hS _ _ hw).2.1)).trans (hS _ _ hw).2.2
    have ht₁ : ((v.1.natAbs.gcd w.1.natAbs).divisors.card : ℝ) ≤
        D * (V (false :: p) : ℝ) ^ δ :=
      (hτ _ hvg).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hvl) hδ.le) hD.le)
    have ht₂ : ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ) ≤
        D * (V (true :: p) : ℝ) ^ δ :=
      (hτ _ hwg).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hwr) hδ.le) hD.le)
    have ht := mul_le_mul ht₁ ht₂ (Nat.cast_nonneg _) (by positivity)
    have hl : 0 ≤ 1 + Real.log (V p) :=
      add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast hV p))
    calc
      _ = C * ∑ s ∈ S p, (modulus s v w : ℝ) ^ (ε - 1) := by
        simp only [factor, Finset.mul_sum]
      _ ≤ C * (4 * ((v.1.natAbs.gcd w.1.natAbs).divisors.card : ℝ) *
          ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ) *
            (V p : ℝ) ^ (2 * ε) * (1 + Real.log (V p)) ^ 3) :=
        mul_le_mul_of_nonneg_left (local_sum_le (S p) (V p) (hS p) v w
          ⟨(hS _ _ hv).1.1,(hS _ _ hv).2.1⟩ hε) hC
      _ = (4 * C * (V p : ℝ) ^ (2 * ε) * (1 + Real.log (V p)) ^ 3) *
          (((v.1.natAbs.gcd w.1.natAbs).divisors.card : ℝ) *
            ((v.2.natAbs.gcd w.2.natAbs).divisors.card : ℝ)) := by ring
      _ ≤ (4 * C * (V p : ℝ) ^ (2 * ε) * (1 + Real.log (V p)) ^ 3) *
          ((D * (V (false :: p) : ℝ) ^ δ) * (D * (V (true :: p) : ℝ) ^ δ)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by dsimp [nodeBudget]; ring

end Ostmann.Arithmetic.PairedFrequencyTreeSum

end

end OAI
