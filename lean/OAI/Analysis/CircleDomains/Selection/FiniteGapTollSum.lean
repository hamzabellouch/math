import OAI.Analysis.CircleDomains.Selection.FiniteGapMultiplicity
import OAI.Analysis.CircleDomains.Rigidity.TypicalAxialDiskTolls

namespace OAI

/-! Counting each remaining disk at most twice gives the exact factor
two for the sum of all retained-gap tolls on one line. -/
open Set Function Filter MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem finite_gap_toll_sum_le {ι κ : Type*} [Fintype ι] [Countable κ]
    (A : ι → Set ℝ) (J : κ → Set ℝ) (w : κ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : Summable (fun j => if (J j).Nonempty then w j else 0))
    (hmult : ∀ j, (Finset.univ.filter (fun i => (J j ∩ A i).Nonempty)).card ≤ 2) :
    (∑ i, ∑' j, if (J j ∩ A i).Nonempty then w j else 0) ≤
      2*∑' j, if (J j).Nonempty then w j else 0 := by
  classical
  let t := fun i j => if (J j ∩ A i).Nonempty then w j else 0
  let b := fun j => if (J j).Nonempty then w j else 0
  have ht (i : ι) : Summable (t i) := by
    apply hs.of_nonneg_of_le
    · intro j
      dsimp only [t]
      split_ifs <;> [exact hw j; exact le_rfl]
    · intro j
      dsimp only [t,b]
      split_ifs with h h'
      · exact le_rfl
      · exact (h' (h.mono inter_subset_left)).elim
      · exact hw j
      · exact le_rfl
  have hcol (j : κ) : (∑ i, t i j) ≤ 2*b j := by
    by_cases hj : (J j).Nonempty
    · have he : (∑ i, t i j) =
          ((Finset.univ.filter (fun i => (J j ∩ A i).Nonempty)).card : ℝ)*w j := by
        simp only [t,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      rw [he]
      dsimp only [b]
      rw [ite_eq_left hj]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmult j) (hw j)
    · have he (i : ι) : t i j = 0 := by
        apply ite_eq_right
        exact fun h => hj (h.mono inter_subset_left)
      simp only [he,Finset.sum_const_zero,b,ite_eq_right hj,mul_zero,le_refl]
  calc
    _ = ∑' j, ∑ i, t i j := (Summable.tsum_finsetSum (fun i _ => ht i)).symm
    _ ≤ ∑' j, 2*b j := Summable.tsum_le_tsum hcol
      (summable_sum (fun i _ => ht i)) (hs.mul_left 2)
    _ = _ := tsum_mul_left

end CircleDomainRigidity

end

end OAI
