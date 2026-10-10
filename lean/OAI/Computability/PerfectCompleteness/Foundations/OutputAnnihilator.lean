import Mathlib.Tactic.NormNum
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Machines.BinaryDualCoordinates

namespace OAI


namespace PerfectCompleteness.OutputAnnihilator

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K : Type*} [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 K] [Fintype (Module.Dual F2 K)]

def bad (W : Submodule F2 K) : Finset (Module.Dual F2 K) :=
  Finset.univ.filter (fun σ => σ ∈ W.dualAnnihilator)

omit [FiniteDimensional F2 K] in
@[simp] theorem mem_bad (W : Submodule F2 K) (σ : Module.Dual F2 K) :
    σ ∈ bad W ↔ σ ∈ W.dualAnnihilator := by
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]

omit [FiniteDimensional F2 K] in
theorem not_mem_bad_iff (W : Submodule F2 K) (σ : Module.Dual F2 K) :
    σ ∉ bad W ↔ σ.comp W.subtype ≠ 0 := by
  rw [mem_bad, TensorCosetEvaluation.annihilator_iff_restriction_zero]

theorem card_bad (W : Submodule F2 K) :
    (bad W).card = 2 ^ (Module.finrank F2 K - Module.finrank F2 W) := by
  calc
    _ = Fintype.card W.dualAnnihilator := by
      rw [Fintype.card_subtype]
      rfl
    _ = Nat.card W.dualAnnihilator := Fintype.card_eq_nat_card
    _ = _ := TensorCosetEvaluation.card_annihilatingCharacters W

omit [FiniteDimensional F2 K] in
theorem card_dual : Fintype.card (Module.Dual F2 K) = 2 ^ Module.finrank F2 K := by
  rw [Module.card_eq_pow_finrank (K := F2), Subspace.dual_finrank_eq]
  rw [show Fintype.card F2 = 2 by decide]

theorem card_dual_eq_bad_mul (W : Submodule F2 K) :
    Fintype.card (Module.Dual F2 K) = (bad W).card * 2 ^ Module.finrank F2 W := by
  rw [card_dual, card_bad, ← pow_add, Nat.sub_add_cancel W.finrank_le]

theorem bad_fraction (W : Submodule F2 K) :
    ((bad W).card : ℝ) / Fintype.card (Module.Dual F2 K) =
      1 / (2 : ℝ) ^ Module.finrank F2 W := by
  have hbad : ((bad W).card : ℝ) ≠ 0 := by
    rw [card_bad]
    positivity
  rw [card_dual_eq_bad_mul W, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    div_mul_eq_div_div, div_self hbad]

theorem bad_fraction_le_of_finrank_le (W : Submodule F2 K) (d : Nat)
    (hd : d ≤ Module.finrank F2 W) :
    ((bad W).card : ℝ) / Fintype.card (Module.Dual F2 K) ≤ 1 / (2 : ℝ) ^ d := by
  rw [bad_fraction]
  exact one_div_le_one_div_of_le (pow_pos (by norm_num) _)
    (pow_le_pow_right₀ (by norm_num) hd)

theorem bad_fraction_le_of_dimension_bound (W : Submodule F2 K) (ℓ r : Nat)
    (hdim : ℓ ≤ Module.finrank F2 W + r) :
    ((bad W).card : ℝ) / Fintype.card (Module.Dual F2 K) ≤
      1 / (2 : ℝ) ^ (ℓ - r) :=
  bad_fraction_le_of_finrank_le W (ℓ - r) (Nat.sub_le_iff_le_add.mpr hdim)

theorem bad_fraction_le_of_codim_le (W : Submodule F2 K) (r : Nat)
    (hcodim : Module.finrank F2 (K ⧸ W) ≤ r) :
    ((bad W).card : ℝ) / Fintype.card (Module.Dual F2 K) ≤
      1 / (2 : ℝ) ^ (Module.finrank F2 K - r) := by
  have hdim : Module.finrank F2 K - r ≤ Module.finrank F2 W := by
    apply Nat.sub_le_iff_le_add.mpr
    calc
      Module.finrank F2 K =
          Module.finrank F2 (K ⧸ W) + Module.finrank F2 W :=
        W.finrank_quotient_add_finrank.symm
      _ ≤ r + Module.finrank F2 W := Nat.add_le_add_right hcodim _
      _ = Module.finrank F2 W + r := Nat.add_comm _ _
  exact bad_fraction_le_of_finrank_le W (Module.finrank F2 K - r) hdim

theorem bad_fraction_lt_of_codim_le (W : Submodule F2 K) (r : Nat) (ρ : ℝ)
    (hcodim : Module.finrank F2 (K ⧸ W) ≤ r)
    (hgap : 1 / (2 : ℝ) ^ (Module.finrank F2 K - r) < ρ / 8) :
    ((bad W).card : ℝ) / Fintype.card (Module.Dual F2 K) < ρ / 8 :=
  (bad_fraction_le_of_codim_le W r hcodim).trans_lt hgap


variable {I : Type*} [Fintype I]

def badMasks (b : Module.Basis I F2 K) (W : Submodule F2 K) : Finset (I → Bool) :=
  Finset.univ.filter
    (fun mask => BinaryDualCoordinates.frequency b mask ∈ W.dualAnnihilator)

omit [FiniteDimensional F2 K] [Fintype (Module.Dual F2 K)] in
@[simp] theorem mem_badMasks (b : Module.Basis I F2 K) (W : Submodule F2 K)
    (mask : I → Bool) :
    mask ∈ badMasks b W ↔ BinaryDualCoordinates.frequency b mask ∈ W.dualAnnihilator := by
  simp only [badMasks, Finset.mem_filter, Finset.mem_univ, true_and]

omit [FiniteDimensional F2 K] [Fintype (Module.Dual F2 K)] in
theorem not_mem_badMasks_iff (b : Module.Basis I F2 K) (W : Submodule F2 K)
    (mask : I → Bool) : mask ∉ badMasks b W ↔
      (BinaryDualCoordinates.frequency b mask).comp W.subtype ≠ 0 := by
  rw [mem_badMasks, TensorCosetEvaluation.annihilator_iff_restriction_zero]

omit [FiniteDimensional F2 K] in
theorem card_badMasks (b : Module.Basis I F2 K) (W : Submodule F2 K) :
    (badMasks b W).card = (bad W).card := by
  calc
    _ = Fintype.card {mask : I → Bool //
        BinaryDualCoordinates.frequency b mask ∈ W.dualAnnihilator} := by
      rw [Fintype.card_subtype]
      rfl
    _ = Fintype.card W.dualAnnihilator := by
      apply Fintype.card_congr
      exact (BinaryDualCoordinates.frequencyEquiv b).subtypeEquiv (fun _ => Iff.rfl)
    _ = _ := by
      rw [Fintype.card_subtype]
      rfl

theorem badMasks_fraction (b : Module.Basis I F2 K) (W : Submodule F2 K) :
    ((badMasks b W).card : ℝ) / Fintype.card (I → Bool) =
      1 / (2 : ℝ) ^ Module.finrank F2 W := by
  rw [card_badMasks, Fintype.card_congr (BinaryDualCoordinates.frequencyEquiv b), bad_fraction]

theorem badMasks_fraction_lt_of_codim_le (b : Module.Basis I F2 K)
    (W : Submodule F2 K) (r : Nat) (ρ : ℝ)
    (hcodim : Module.finrank F2 (K ⧸ W) ≤ r)
    (hgap : 1 / (2 : ℝ) ^ (Module.finrank F2 K - r) < ρ / 8) :
    ((badMasks b W).card : ℝ) / Fintype.card (I → Bool) < ρ / 8 := by
  rw [card_badMasks, Fintype.card_congr (BinaryDualCoordinates.frequencyEquiv b)]
  exact bad_fraction_lt_of_codim_le W r ρ hcodim hgap

end
end PerfectCompleteness.OutputAnnihilator

end OAI
