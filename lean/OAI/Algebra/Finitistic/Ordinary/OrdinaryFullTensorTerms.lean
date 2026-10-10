import OAI.Algebra.Finitistic.Ordinary.OrdinaryTwoSidedTensor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorDifferential
import OAI.Algebra.Finitistic.Ordinary.OrdinaryIntegerResolution

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

instance BimoduleO.commuteRightTensor : SMulCommClass Bᵐᵒᵖ (B ⊗[k] ChainAlgebra k l) (BimoduleO P a l) :=
  ⟨fun r x v => (smul_comm x r v).symm⟩

/-- Every degree of Q_T tensor_BC O, carrying the actual outside B-actions. -/
abbrev FullTensorTerm (n : ℕ) := TwoSidedTensor k (B ⊗[k] ChainAlgebra k l) B Bᵐᵒᵖ
  (TensorResolution.term k B l n) (BimoduleO P a l)

namespace FullTensorTerm
open ChainAlgebra

/-- Supported extended ideals are the same right ideals as the finite vertex terms. -/
def supportedIdealEquiv (n : ℕ) (hn : n ≤ l) :
    TensorResolution.term k B l n ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
      IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (vertex k l ⟨n,by omega⟩)) where
  toFun x := ⟨x.val, by
    have hx := x.property
    change TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n) * x.val = x.val at hx
    rw [extendedVertex,dite_eq_left hn] at hx
    exact hx⟩
  invFun x := ⟨x.val, by
    change TensorIdeal.vertex (k := k) (B := B) (extendedVertex k l n) * x.val = x.val
    rw [extendedVertex,dite_eq_left hn]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def finiteModel (i : Fin (l+1)) :
    TwoSidedTensor k (B ⊗[k] ChainAlgebra k l) B Bᵐᵒᵖ
      (IdempotentTensor.rightIdeal (TensorIdeal.vertex (k := k) (B := B) (vertex k l i)))
      (BimoduleO P a l) ≃ₗ[Enveloping k B] VertexTensor P a l i where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual degreewise B-bimodule comparison throughout the supported range. -/
def supportedEquiv (n : ℕ) (hn : n ≤ l) : FullTensorTerm P a l n ≃ₗ[Enveloping k B] P.X (a+(n:ℤ)) :=
  (TwoSidedTensor.congrLeft (k := k) (S := B) (T := Bᵐᵒᵖ) (N := BimoduleO P a l)
    (supportedIdealEquiv (k := k) (B := B) l n hn) (fun _ _ => rfl)).trans
      ((finiteModel P a l ⟨n,by omega⟩).trans (VertexTensor.bimoduleEquiv P a l ⟨n,by omega⟩))

theorem subsingleton_above (n : ℕ) (hn : l < n) : Subsingleton (FullTensorTerm P a l n) := by
  let : Subsingleton (TensorResolution.term k B l n) :=
    (ModuleCat.isZero_iff_subsingleton).mp (TensorResolution.term_vanishes k B l n hn)
  exact inferInstanceAs (Subsingleton (BalancedTensor.Tensor k (B ⊗[k] ChainAlgebra k l)
    (TensorResolution.term k B l n) (BimoduleO P a l)))

/-- Use precisely the source's upper support bound for all remaining degrees. -/
def outsideEquiv (n : ℕ) (hn : l < n) (hP : IsZero (P.X (a+(n:ℤ)))) :
    FullTensorTerm P a l n ≃ₗ[Enveloping k B] P.X (a+(n:ℤ)) := by
  letI := subsingleton_above P a l n hn
  letI : Subsingleton (P.X (a+(n:ℤ))) := ModuleCat.isZero_iff_subsingleton.mp hP
  exact { toFun := fun _ => 0
          invFun := fun _ => 0
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _
          map_add' := fun _ _ => Subsingleton.elim _ _
          map_smul' := fun _ _ => Subsingleton.elim _ _ }

/-- No extra support assumptions: P is required to vanish only above a+l here. -/
def termEquiv (hP : ∀ n : ℕ, l < n → IsZero (P.X (a+(n:ℤ)))) (n : ℕ) :
    FullTensorTerm P a l n ≃ₗ[Enveloping k B] P.X (a+(n:ℤ)) :=
  if hn : n ≤ l then supportedEquiv P a l n hn else outsideEquiv P a l n (by omega) (hP n (by omega))
end FullTensorTerm
end LittleFinitistic.OrdinarySimulation

end

end OAI
