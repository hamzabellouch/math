import OAI.MathematicalPhysics.Heisenberg.SpinTensorRepresentation

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open TensorUnits
variable {d ℓ : ℕ}

lemma plus_coefficient (k : Fin ℓ) :
    Real.sqrt (((ℓ-k.val:ℕ):ℝ)*(k.val+1))=
      Real.sqrt ((ℓ/2:ℝ)*(ℓ/2+1)-magneticLevel ℓ k.castSucc*(magneticLevel ℓ k.castSucc+1)) := by
  congr 1
  rw [Nat.cast_sub k.isLt.le]
  simp only [magneticLevel,Fin.val_castSucc]
  ring

lemma oneSite_plus (x : Site d) :
    liftLinear (localUnit d ℓ x) (SpinSlots.physicalPlus ℓ)=spinPlus d ℓ x := by
  change (∑ a : Level ℓ,∑ b : Level ℓ,
    (if a.val=b.val+1 then Real.sqrt (((ℓ-b.val:ℕ):ℝ)*(b.val+1)) else 0) • localUnit d ℓ x a b)=_
  rw [Finset.sum_comm,Fin.sum_univ_castSucc]
  have hsum (k : Fin ℓ) :
      (∑ a : Level ℓ,(if a.val=k.val+1 then Real.sqrt (((ℓ-k.val:ℕ):ℝ)*(k.val+1)) else 0) • localUnit d ℓ x a k.castSucc)=
        Real.sqrt (((ℓ-k.val:ℕ):ℝ)*(k.val+1)) • localUnit d ℓ x k.succ k.castSucc := by
    rw [Finset.sum_eq_single k.succ]
    · simp only [Fin.val_succ,ite_true]
    · intro a _ ha
      have hne : a.val≠k.val+1:=fun he=>ha (Fin.ext he)
      rw [ite_eq_right hne,zero_smul]
    · exact fun h=>False.elim (h (Finset.mem_univ _))
  have hlast : (∑ a : Level ℓ,(if a.val=(Fin.last ℓ).val+1 then Real.sqrt (((ℓ-(Fin.last ℓ).val:ℕ):ℝ)*((Fin.last ℓ).val+1)) else 0) • localUnit d ℓ x a (Fin.last ℓ))=0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [ite_eq_right (by have := a.isLt; simp only [Fin.val_last]; omega),zero_smul]
  simp only [Fin.val_castSucc,hsum,hlast,add_zero,spinPlus]
  apply Finset.sum_congr rfl
  intro k _
  rw [plus_coefficient]
  exact (IsScalarTower.algebraMap_smul ℂ _ _).symm

lemma oneSite_transpose (x : Site d) (M : Matrix (Level ℓ) (Level ℓ) ℝ) :
    liftLinear (localUnit d ℓ x) M.transpose=star (liftLinear (localUnit d ℓ x) M) := by
  simp only [liftLinear,LinearMap.coe_mk,AddHom.coe_mk,Matrix.transpose_apply,star_sum,star_smul,
    star_trivial,star_localUnit]
  rw [Finset.sum_comm]

variable {X : Type} [Fintype X] [DecidableEq X]
lemma finiteRepresentation_plus (site : X → Site d) (hinj : Function.Injective site) (x : X) :
    finiteRepresentation site hinj (TensorMatrix.onsite x (SpinSlots.physicalPlus ℓ))=spinPlus d ℓ (site x) := by
  rw [finiteRepresentation_onsite,oneSite_plus]

lemma finiteRepresentation_minus (site : X → Site d) (hinj : Function.Injective site) (x : X) :
    finiteRepresentation site hinj (TensorMatrix.onsite x (SpinSlots.physicalPlus ℓ).transpose)=spinMinus d ℓ (site x) := by
  rw [finiteRepresentation_onsite,oneSite_transpose,oneSite_plus]
  rfl

lemma xy_bond (d ℓ : ℕ) (x y : Site d) :
    spinX d ℓ x*spinX d ℓ y+spinY d ℓ x*spinY d ℓ y=
      (1/2:ℝ) • (spinPlus d ℓ x*spinMinus d ℓ y+spinMinus d ℓ x*spinPlus d ℓ y) := by
  have hc : (1/(2*Complex.I):ℂ)*(1/(2*Complex.I))= -(1/4:ℂ) := by
    simp only [one_div,mul_inv_rev,Complex.inv_I]
    ring_nf
    norm_num [Complex.I_sq]
  rw [spinX,spinX,spinY,spinY,smul_mul_smul_comm,smul_mul_smul_comm,hc]
  rw [←IsScalarTower.algebraMap_smul ℂ (1/2:ℝ)]
  norm_num only [map_div₀,map_one,map_ofNat]
  simp only [mul_add,add_mul,mul_sub,sub_mul]
  module

lemma finiteRepresentation_bond (site : X → Site d) (hinj : Function.Injective site) (x y : X) :
    finiteRepresentation site hinj (SlotTensor.spinBond ℓ x y)=bond d ℓ (site x) (site y) := by
  simp only [SlotTensor.spinBond,map_add,map_smul,map_mul,
    finiteRepresentation_plus,finiteRepresentation_minus,finiteRepresentation_z]
  rw [←xy_bond]
  rfl

end Heisenberg
end
end

end OAI
