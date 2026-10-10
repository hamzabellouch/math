import OAI.NumberTheory.Ostmann.Construction.DiagonalCountBudget
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalNormalizer
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalSplit

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
open Filter
namespace Ostmann.Construction
open Conclusion DiagonalPermutationCount

def diagonalMatchingOverhead (m k l : ℕ) : ℝ :=
  (((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)*
    (((2^l:ℕ):ℝ)^(2*(2^l)))

theorem selected_diagonal_bad_count_budget_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l : ℕ,C.selectedDiagonalNormalizer l*
        (Nat.card {e // InitialSourceChoice.diagonalBadPermutation (2*(bulkSize k L/2)) k l e}:ℝ)≤
      diagonalMatchingOverhead (bulkSize k L) k l*
        Real.exp (-stepGap BD Bz k L l+
          (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+36)*
            (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))) := by
  filter_upwards [remainingNormalization_bound_eventually d Bs BD Bz hk,
    eventually_gt_atTop (0:ℝ),(bulkSize_tendsto_atTop hk).eventually_gt_atTop (0:ℝ)] with L hN hL hm
  intro E C hG hGu hcl hcu hb hd l
  have hmN : 0 < bulkSize k L := by exact_mod_cast hm
  have hz : 0 < bulkScale k := by unfold bulkScale; positivity
  have heven : 2*(bulkSize k L/2)=bulkSize k L := by
    obtain ⟨n,hn⟩ := bulkSize_even k L
    omega
  have hcount := remaining_transfer_bad_normalized_count (bulkSize k L) k l L (bulkScale k)
    hmN hL hz (selected_bulk_ratio_le k L hL)
  have hnormal := hN E C hG hGu hcl hcu hb hd l
  have hnormal34 : C.remainingNormalization (remainingTemplate (bulkSize k L) k l)≤
      Real.exp (34*(((2^l:ℕ):ℝ)*(bulkSize k L:ℝ)))/L^(2^l*bulkSize k L) := by
    refine hnormal.trans ?_
    apply div_le_div_of_nonneg_right _ (pow_nonneg hL.le _)
    apply Real.exp_le_exp.mpr
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right counterpartNormalizationConstant_le
        (show 0≤(2:ℝ)^l*(bulkSize k L:ℝ) by positivity)
  unfold InitialSourceChoice.selectedDiagonalNormalizer InitialSourceChoice.diagonalBadPermutation
  rw [heven]
  let n : ℝ := (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate (bulkSize k L) k l)) //
    PreservesRemainingBands (remainingTemplate (bulkSize k L) k l) e ∧
      TransferBadArrangement (remainingBulkPermutation (bulkSize k L) k l e)}:ℝ)
  have hn : 0≤n := Nat.cast_nonneg _
  change (C.remainingNormalization (remainingTemplate (bulkSize k L) k l)*
    Real.exp (-stepGap BD Bz k L l))*n≤_
  calc
    _ ≤ (Real.exp (34*(((2^l:ℕ):ℝ)*(bulkSize k L:ℝ)))/L^(2^l*bulkSize k L)*
        Real.exp (-stepGap BD Bz k L l))*n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnormal34 (Real.exp_pos _).le) hn
    _ = Real.exp (34*(((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))-stepGap BD Bz k L l)*
        (n/L^(2^l*bulkSize k L)) := by rw [Real.exp_sub,Real.exp_neg]; ring
    _ ≤ Real.exp (34*(((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))-stepGap BD Bz k L l)*
        (diagonalMatchingOverhead (bulkSize k L) k l*
          Real.exp ((Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+2)*
            (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ)))) :=
      mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
    _ = _ := by
      rw [←mul_assoc,mul_comm (Real.exp _) (diagonalMatchingOverhead _ _ _),mul_assoc,←Real.exp_add]
      congr 2
      ring

end Ostmann.Construction

end

end OAI
