import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodNormalizerBasic

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction
open Conclusion DiagonalPermutationCount

theorem selected_diagonal_good_normalizer_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) (hD : 0≤BD) (hz : 0≤Bz) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,C.selectedDiagonalNormalizer l*
        (Nat.card {e : Equiv.Perm (RemainingIndex
          (remainingTemplate (2*(bulkSize k L/2)) k l)) //
          PreservesRemainingBands (remainingTemplate (2*(bulkSize k L/2)) k l) e}:ℝ)≤
        Real.exp (selectedDiagonalGoodRate k*(bulkSize k L:ℝ)) := by
  filter_upwards [remainingNormalization_bound_eventually d Bs BD Bz hk,
    remaining_nonbulk_factorial_absorbed_eventually hk,
    eventually_gt_atTop (0:ℝ)] with L hN hF hL
  intro E C hG hGu hcl hcu hb hd l hl
  have hscale : 0<bulkScale k := lt_of_lt_of_le zero_lt_one (bulkScale_one_le hk)
  have heven : 2*(bulkSize k L/2)=bulkSize k L := by
    obtain ⟨n,hn⟩ := bulkSize_even k L
    omega
  have hcount := remaining_total_normalized_count (bulkSize k L) k l L (bulkScale k)
    hL hscale (selected_bulk_ratio_le k L hL)
  have hnormal := hN E C hG hGu hcl hcu hb hd l
  have hnormal34 : C.remainingNormalization (remainingTemplate (bulkSize k L) k l)≤
      Real.exp (34*((2:ℝ)^l*(bulkSize k L:ℝ)))/L^(2^l*bulkSize k L) := by
    refine hnormal.trans ?_
    apply div_le_div_of_nonneg_right _ (pow_nonneg hL.le _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right counterpartNormalizationConstant_le (by positivity)
  have hselected : C.selectedDiagonalNormalizer l≤
      Real.exp (34*((2:ℝ)^l*(bulkSize k L:ℝ)))/L^(2^l*bulkSize k L) := by
    unfold InitialSourceChoice.selectedDiagonalNormalizer
    rw [heven]
    refine le_trans ?_ hnormal34
    exact mul_le_of_le_one_right (C.remainingNormalization_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (stepGap_nonneg_of_budgets hk hD hz L l)))
  rw [heven]
  let n : ℝ := (Nat.card {e : Equiv.Perm (RemainingIndex (remainingTemplate (bulkSize k L) k l)) //
    PreservesRemainingBands (remainingTemplate (bulkSize k L) k l) e}:ℝ)
  have hn : 0≤n := Nat.cast_nonneg _
  change C.selectedDiagonalNormalizer l*n≤_
  have hcount' : n/L^(2^l*bulkSize k L)≤
      (((remainingTemplate (bulkSize k L) k l).length+1-2^l*bulkSize k L).factorial:ℝ)*
        Real.exp (((2:ℝ)^l*(bulkSize k L:ℝ))*Real.log ((2:ℝ)^l*bulkScale k)) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hcount
  calc
    _ ≤ (Real.exp (34*((2:ℝ)^l*(bulkSize k L:ℝ)))/L^(2^l*bulkSize k L))*n :=
      mul_le_mul_of_nonneg_right hselected hn
    _ = Real.exp (34*((2:ℝ)^l*(bulkSize k L:ℝ)))*(n/L^(2^l*bulkSize k L)) := by ring
    _ ≤ Real.exp (34*((2:ℝ)^l*(bulkSize k L:ℝ)))*
        ((((remainingTemplate (bulkSize k L) k l).length+1-2^l*bulkSize k L).factorial:ℝ)*
          Real.exp (((2:ℝ)^l*(bulkSize k L:ℝ))*Real.log ((2:ℝ)^l*bulkScale k))) :=
      mul_le_mul_of_nonneg_left hcount' (Real.exp_pos _).le
    _ ≤ Real.exp (34*((2:ℝ)^l*(bulkSize k L:ℝ)))*
        (Real.exp ((2:ℝ)^l*(bulkSize k L:ℝ))*
          Real.exp (((2:ℝ)^l*(bulkSize k L:ℝ))*Real.log ((2:ℝ)^l*bulkScale k))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hF l hl) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp ((35+Real.log ((2:ℝ)^l*bulkScale k))*((2:ℝ)^l*(bulkSize k L:ℝ))) := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (selectedDiagonalGoodRate_dominates hk hl (bulkSize k L))

end Ostmann.Construction

end

end OAI
