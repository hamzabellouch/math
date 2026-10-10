import OAI.Analysis.Laughlin.FourBody.PhysicalGram
import OAI.Analysis.Laughlin.Operators.PositiveFockLift

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def fourOccupationCreate (Q D : ℕ) (A : FourOccupation Q D) : Module.End ℂ (Space Q) :=
  let l := occupationFourLabels Q A.val A.property.1
  create (l 0)*create (l 1)*create (l 2)*create (l 3)

noncomputable def fourOccupationEnd (Q D : ℕ) (A : FourOccupation Q D) : Module.End ℂ (Space Q) :=
  let l := occupationFourLabels Q A.val A.property.1
  annihilate (l 3)*annihilate (l 2)*annihilate (l 1)*annihilate (l 0)

theorem fourOccupation_adjoint (Q D : ℕ) (A : FourOccupation Q D) (x y : Space Q) :
    occupationInner Q x (fourOccupationCreate Q D A y) =
      occupationInner Q (fourOccupationEnd Q D A x) y := by
  simp only [fourOccupationCreate,fourOccupationEnd,Module.End.mul_apply,create_annihilate_adjoint_right]

theorem fourOccupationCreate_mul (Q D : ℕ) (A : FourOccupation Q D) (x : Space Q) :
    fourOccupationCreate Q D A x = occupationBasis Q A.val * x := by
  rw [occupationBasis_four Q A.val A.property.1]
  simp [fourOccupationCreate,create,mul_assoc]

theorem limitFourColumn_mul_adjoint (Q r D : ℕ) (x y : Space Q) :
    occupationInner Q x (limitFourColumn Q r D * y) =
      occupationInner Q (limitFourCopyEnd Q r D x) y := by
  simp only [limitFourColumn,Finset.sum_mul,smul_mul_assoc]
  simp only [limitFourCopyEnd,weightedFourEnd,limitFourEnd,limitPairEnd,pairEnd,
    LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,Complex.star_def,Complex.conj_ofReal]
  simp only [create,LinearMap.coe_mk,AddHom.coe_mk,mul_one,mul_assoc]
  simp only [show ∀ (i : Fin (Q+1)) (v : Space Q), (ExteriorAlgebra.ι ℂ) (mode i)*v=create i v from by intros; rfl,
    create_annihilate_adjoint_right]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  push_cast
  ring

theorem limitFourColumn_expansion (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r) :
    limitFourColumn Q r D = ∑ A : FourOccupation Q D,
      (fourOccupationCoefficient Q r D A.val : ℂ) • occupationBasis Q A.val := by
  classical
  conv_lhs => rw [← (occupationBasis Q).sum_repr (limitFourColumn Q r D)]
  simp_rw [limitFourColumn_occupation_coefficient Q r D hr hor]
  let P := fun A : Finset (Fin (Q+1)) => A.card=4 ∧ (∑ i ∈ A, i.val)=D+1
  rw [← Finset.sum_subset (Finset.filter_subset P Finset.univ) (f := fun A =>
    (fourOccupationCoefficient Q r D A : ℂ) • occupationBasis Q A)]
  · exact Finset.sum_subtype _ (by simp [P]) _
  · intro A hA hn
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hn
    by_cases hc : A.card=4
    · have hw : (∑ i ∈ A, i.val) ≠ D+1 := by intro hw; exact hn ⟨hc,hw⟩
      simp [fourOccupationCoefficient,hc,hw]
    · simp [fourOccupationCoefficient,hc]

end Laughlin.Fock

end OAI
