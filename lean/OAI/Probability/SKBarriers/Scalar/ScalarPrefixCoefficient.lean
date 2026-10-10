import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarEarlyMoment
import OAI.Probability.SKBarriers.Scalar.ScalarLevelRepresentation

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarLevelField_axis (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) (i : Fin n) :
    scalarLevelField n v j (coordinateAxis n i)=if i.val<j.val then v i else 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [scalarLevelField_last]
      simp only [Fin.val_last, i.isLt,ite_true]
      change parameter (n+1) (coordinateAxis (n+1) i)+coordinateLinear (n+1) v (coordinateAxis (n+1) i)=v i
      rw [parameter_coordinateAxis (n+1) i,coordinateLinear_coordinateAxis]
      simp
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [scalarLevelField,Fin.lastCases_castSucc,coordinateAxis_last,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',map_zero,
          Fin.val_last,Fin.val_castSucc]
        rw [ite_eq_right (by omega)]
      · simp only [scalarLevelField,Fin.lastCases_castSucc,coordinateAxis_castSucc,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ih,
          Fin.val_castSucc]

theorem scalarLevelField_vector (n : ℕ) (v a : Fin n → ℝ) (j : Fin (n+1)) :
    scalarLevelField n v j (coordinateVector n a)=∑ i, if i.val<j.val then a i*v i else 0 := by
  simp only [coordinateVector,map_sum,map_smul,smul_eq_mul,scalarLevelField_axis]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem hierarchyAtom_prefix (n : ℕ) (m : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin (n+1), if j.val ≤ i.val then hierarchyAtom n m 1 j else 0)=m i := by
  suffices H : ∀ u : ℝ, (∑ j : Fin (n+1), if j.val ≤ i.val then hierarchyAtom n m u j else 0)=m i by exact H 1
  intro u
  induction n generalizing u with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hi : ¬(n+1 ≤ i.val) := by omega
    simp only [Fin.val_last,ite_eq_right hi,add_zero,Fin.val_castSucc,hierarchyAtom,Fin.lastCases_castSucc]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.val_last]
      simp only [show ∀ j : Fin (n+1), j.val ≤ n from fun j => by omega,ite_true]
      rw [hierarchyAtom_sum]
    · simpa only [Fin.val_castSucc] using ih (fun j => m j.castSucc) i (m (Fin.last n))

end SK.Analytic

end
end

end OAI
