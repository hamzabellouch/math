import OAI.NumberTheory.TwoPoint.Walks.WitnessCatalogCost

namespace OAI

/-! Explicit finite metadata for splitting one recorded word into witness paths. -/

namespace TwoPointCorrelations

open Finset

abbrev WitnessSegmentation (n R : ℕ) :=
  Fin (R + 1) × (Fin n → Fin (R + 1)) × (Fin n → Fin (R + 1))

lemma card_witnessSegmentation (n R : ℕ) :
    Fintype.card (WitnessSegmentation n R) = (R + 1) ^ (2 * n + 1) := by
  simp only [WitnessSegmentation, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [show 2 * n + 1 = n + n + 1 by omega, pow_add, pow_add]
  ring

lemma witnessSegmentation_cost (n R : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hn : (n : ℝ) ≤ 4 * L) (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (WitnessSegmentation n R) : ℝ) ≤
      Real.exp (18 * L * (Real.log L) ^ 2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
      Real.exp_add, Real.exp_log hLp]
    ring
  calc
    _ = ((R : ℝ) + 1) ^ (2 * n + 1) := by
      rw [card_witnessSegmentation]
      push_cast
      rfl
    _ ≤ (L ^ (2 : ℕ)) ^ (2 * n + 1) :=
      pow_le_pow_left₀ (by positivity) hR _
    _ = Real.exp (((2 * n + 1 : ℕ) : ℝ) * (2 * Real.log L)) := by
      rw [Real.exp_nat_mul, he]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      push_cast
      have hs : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
      have hcoef : 4 * (n : ℝ) + 2 ≤ 18 * L := by linarith
      have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ Real.log L by linarith)
      have hm' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 18 * L by positivity)
      nlinarith

/-- A common scalar bound with the exact finite cardinality pays for every record. -/
lemma sum_le_of_card_mul_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (B : ℝ) (hf : ∀ i, (Fintype.card ι : ℝ) * f i ≤ B) :
    ∑ i, f i ≤ B := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (Fintype.card ι : ℝ) * (∑ i, f i) = ∑ i, (Fintype.card ι : ℝ) * f i :=
      mul_sum _ _ _
    _ ≤ ∑ _i : ι, B := sum_le_sum (fun i _ => hf i)
    _ = (Fintype.card ι : ℝ) * B := by simp

end TwoPointCorrelations

end OAI
