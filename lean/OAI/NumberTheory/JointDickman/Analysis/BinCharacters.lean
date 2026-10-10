import OAI.NumberTheory.JointDickman.Amplification.FiniteStatistics
import OAI.NumberTheory.JointDickman.Amplification.BinDecorrelation

namespace OAI

/-! # Characters of the finite bin-count group are unit bin labels -/
namespace JointDickman
open Finset Classical
open scoped Fin.NatCast

noncomputable def binCharacterNodes {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    (i : Fin (J-1)) : ℂ := χ (Pi.single i 1)

theorem binCharacterNodes_norm {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    (i : Fin (J-1)) : ‖binCharacterNodes χ i‖ = 1 := χ.norm_apply _

theorem binCharacter_apply {J : ℕ} (χ : AddChar (BinCountState J) ℂ) (r : BinCountState J) :
    χ r = ∏ i, binCharacterNodes χ i^(r i).val := by
  have hn (n : ℕ) : n • (1 : Fin (J+1)) = (n : Fin (J+1)) := by
    induction n with
    | zero => simp
    | succ n ih => simp only [succ_nsmul,ih,Nat.cast_add,Nat.cast_one]
  have he : r = ∑ i : Fin (J-1), (r i).val • Pi.single i (1 : Fin (J+1)) := by
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply]
    simp only [Pi.single_apply,smul_ite,smul_zero,sum_ite_eq,mem_univ,ite_true]
    rw [hn,Fin.cast_val_eq_self]
  conv_lhs => rw [he]
  have hsum (s : Finset (Fin (J-1))) :
      χ (∑ i ∈ s, (r i).val • Pi.single i (1 : Fin (J+1))) =
        ∏ i ∈ s, χ ((r i).val • Pi.single i (1 : Fin (J+1))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [sum_insert hi,prod_insert hi,χ.map_add_eq_mul,ih]
  rw [hsum]
  apply prod_congr rfl
  intro i _
  exact χ.map_nsmul_eq_pow _ _

theorem binCharacter_canonical {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    {x : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hcounts : ∀ i : Fin (J-1), (canonicalBinVector J x n i).val = binCount (primeBin x J (i.val+1)) n) :
    χ (canonicalBinVector J x n) =
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) (binCharacterNodes χ) n := by
  rw [binCharacter_apply,binLabel_apply hn]
  apply prod_congr rfl
  intro i _
  rw [hcounts i]

theorem binCharacter_mean {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    (ν : BinCountState J → ℝ) :
    binDistributionMean ν (binCharacterNodes χ) = ∑ r, (ν r : ℂ)*χ r := by
  simp only [binDistributionMean,binCharacter_apply]

end JointDickman

end OAI
