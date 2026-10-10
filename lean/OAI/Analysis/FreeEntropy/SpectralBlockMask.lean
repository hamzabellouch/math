import OAI.Analysis.FreeEntropy.MatrixHilbertSchmidt

namespace OAI

noncomputable section
open Finset MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {p d : ℕ}
 def blockMask (f : Fin d → Fin p) : Finset (Fin (p+1) × Fin d × Fin d) :=
    univ.filter (fun q => q.1.val<p ∧ f q.2.1=f q.2.2)
 def balancedBlocks (f : Fin d → Fin p) : Prop :=
    ∀l, p*(univ.filter (fun j => f j=l)).card≤2*d
 theorem blockMask_card (f : Fin d → Fin p) :
    (blockMask f).card = p*∑j : Fin d,(univ.filter (fun k => f k=f j)).card := by
  classical
  rw [blockMask,card_filter]
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last,lt_self_iff_false,false_and,ite_false,sum_const_zero,add_zero,
    Fin.val_castSucc,Fin.is_lt,true_and]
  have he : (∑j : Fin d,∑k : Fin d,if f j=f k then 1 else 0)=
      ∑j : Fin d,(univ.filter (fun k => f k=f j)).card := by
    apply sum_congr rfl
    intro j _
    simp only [card_filter,eq_comm]
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
 theorem blockMask_card_le (f : Fin d → Fin p) (hf : balancedBlocks f) :
    (blockMask f).card≤2*d^2 := by
  rw [blockMask_card,mul_sum]
  calc
    _ ≤ ∑j : Fin d,2*d := sum_le_sum (fun j _ => hf (f j))
    _ = _ := by simp; ring
 theorem blockMask_matrixEnergy (f : Fin d → Fin p) (a : MatrixCoordinates (p+1) d) :
    ‖coordinateMask (blockMask f) a‖^2 =
      ∑i : Fin p,∑j : Fin d,∑k : Fin d,if f j=f k then Complex.normSq (hermitianMatrix a i.castSucc j k) else 0 := by
  classical
  rw [coordinateMask_sq,blockMask,sum_filter]
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last,lt_self_iff_false,false_and,ite_false,sum_const_zero,add_zero,
    Fin.val_castSucc,Fin.is_lt,true_and]
  apply sum_congr rfl
  intro i _
  simp_rw [hermitianMatrix_normSq]
  have he : (∑j : Fin d,∑k : Fin d,if f j=f k then a (i.castSucc,k,j)^2 else 0)=
      ∑j : Fin d,∑k : Fin d,if f j=f k then a (i.castSucc,j,k)^2 else 0 := by
    rw [sum_comm]
    congr 1
    funext k
    apply sum_congr rfl
    intro j _
    simp only [eq_comm]
  have hp (j k : Fin d) : (if f j=f k then (a (i.castSucc,j,k)^2+a (i.castSucc,k,j)^2)/2 else 0) =
      ((if f j=f k then a (i.castSucc,j,k)^2 else 0)+(if f j=f k then a (i.castSucc,k,j)^2 else 0))/2 := by split_ifs <;> ring
  conv_rhs => simp only [hp,← sum_div,sum_add_distrib]
  rw [he]
  ring
end FiniteEntropySeparation

end

end OAI
