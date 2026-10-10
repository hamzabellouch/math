import OAI.Analysis.CharacterCriterion.TensorSections

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.FourLegSymmetries
open scoped CStarAlgebra ComplexOrder Matrix Kronecker
open MatrixTensor MatrixPermutationPath
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
abbrev Index (P Q : Type*) := (P×Q)×(P×Q)
abbrev Algebra (P Q : Type*) := MatrixTensor.Mat (Index P Q)
def hflip : Equiv.Perm (Index P Q) where
  toFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  invFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
def kflip : Equiv.Perm (Index P Q) where
  toFun x := ((x.1.1,x.2.2),(x.2.1,x.1.2))
  invFun x := ((x.1.1,x.2.2),(x.2.1,x.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
def H : unitary (Algebra P Q) := perm hflip
def K : unitary (Algebra P Q) := perm kflip
lemma H_selfadjoint : star (H (P:=P) (Q:=Q) : Algebra P Q)=(H (P:=P) (Q:=Q) : Algebra P Q) := by
  change (hflip⁻¹.permMatrix ℂ)ᴴ = hflip⁻¹.permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  rfl
lemma K_selfadjoint : star (K (P:=P) (Q:=Q) : Algebra P Q)=(K (P:=P) (Q:=Q) : Algebra P Q) := by
  change (kflip⁻¹.permMatrix ℂ)ᴴ = kflip⁻¹.permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  rfl
lemma flips_commute : Commute (H (P:=P) (Q:=Q)) K := by
  change perm hflip * perm kflip=perm kflip*perm hflip
  rw [←perm_mul,←perm_mul]
  congr 1
lemma flip_product : H (P:=P) (Q:=Q)*K=perm (Equiv.prodComm (P×Q) (P×Q)) := by
  rw [H,K,←perm_mul]
  rfl
lemma conj_flip_left (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)*K) (MatrixTensor.leftMatrix a)=MatrixTensor.rightMatrix a := by
  rw [flip_product,perm_conjugation]
  ext i j
  change a i.2 j.2 * (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 * a i.2 j.2
  exact mul_comm _ _

lemma conj_K_left_left (a : MatrixTensor.Mat P) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a))=
      MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a) := by
  rw [K,perm_conjugation]
  ext i j
  change (a i.1.1 j.1.1 * (1:Matrix Q Q ℂ) i.2.2 j.2.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) =
    (a i.1.1 j.1.1 * (1:Matrix Q Q ℂ) i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) i.2 j.2
  simp only [Matrix.one_apply,Prod.mk.injEq]
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

lemma conj_H_right_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.rightMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix b) := by
  rw [H,perm_conjugation]
  ext i j
  change (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) *
    ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.2.2 j.2.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

end KirchbergRordam.FourLegSymmetries
namespace KirchbergRordam.FourLegSymmetries
open MatrixTensor MatrixPermutationPath
open scoped CStarAlgebra ComplexOrder Matrix Kronecker TensorProduct
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
lemma H_decompose : (H (P:=P) (Q:=Q) : Algebra P Q) =
    ∑ ij : P×P, MatrixTensor.leftMatrix (MatrixTensor.leftMatrix (κ:=Q) (unit ij.1 ij.2))*
      MatrixTensor.rightMatrix (MatrixTensor.leftMatrix (κ:=Q) (unit ij.2 ij.1)) := by
  simp_rw [legs_product]
  ext i j
  change (hflip⁻¹.permMatrix ℂ) i j =
    (∑ ab : P×P, Matrix.kronecker (Matrix.kronecker (Matrix.single ab.1 ab.2 (1:ℂ)) 1)
      (Matrix.kronecker (Matrix.single ab.2 ab.1 (1:ℂ)) 1)) i j
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,hflip,Equiv.Perm.inv_def,Equiv.coe_fn_symm_mk,Prod.mk.injEq,
    Matrix.sum_apply]
  simp [←Finset.univ_product_univ,Finset.sum_product,ite_and,Matrix.single_apply,Matrix.one_apply,eq_comm]
  split_ifs <;> simp_all
lemma K_decompose : (K (P:=P) (Q:=Q) : Algebra P Q) =
    ∑ ij : Q×Q, MatrixTensor.leftMatrix (MatrixTensor.rightMatrix (ι:=P) (unit ij.1 ij.2))*
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix (ι:=P) (unit ij.2 ij.1)) := by
  simp_rw [legs_product]
  ext i j
  change (kflip⁻¹.permMatrix ℂ) i j =
    (∑ ab : Q×Q, Matrix.kronecker (Matrix.kronecker 1 (Matrix.single ab.1 ab.2 (1:ℂ)))
      (Matrix.kronecker 1 (Matrix.single ab.2 ab.1 (1:ℂ)))) i j
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,kflip,Equiv.Perm.inv_def,Equiv.coe_fn_symm_mk,Prod.mk.injEq,
    Matrix.sum_apply]
  simp [←Finset.univ_product_univ,Finset.sum_product,ite_and,Matrix.single_apply,Matrix.one_apply,eq_comm]
  split_ifs <;> simp_all
lemma H_mem : (H (P:=P) (Q:=Q) : Algebra P Q)∈
    tensorRange (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range := by
  rw [H_decompose]
  apply Subalgebra.sum_mem
  intro ij _
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
lemma K_mem : (K (P:=P) (Q:=Q) : Algebra P Q)∈
    tensorRange (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range := by
  rw [K_decompose]
  apply Subalgebra.sum_mem
  intro ij _
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
lemma conj_K_left_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix b) := by
  rw [K,perm_conjugation]
  ext i j
  change ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.2.2 j.2.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all
lemma conj_H_left_left (a : MatrixTensor.Mat P) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a))=
      MatrixTensor.rightMatrix (MatrixTensor.leftMatrix a) := by
  rw [H,perm_conjugation]
  ext i j
  change (a i.2.1 j.2.1 * (1:Matrix Q Q ℂ) i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.1.1,i.2.2) (j.1.1,j.2.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    (a i.2.1 j.2.1 * (1:Matrix Q Q ℂ) i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all
lemma conj_H_left_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b) := by
  rw [H,perm_conjugation]
  ext i j
  change ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.1.1,i.2.2) (j.1.1,j.2.2) =
    ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) i.2 j.2
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

lemma K_cross_mem (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix a) ∈
      tensorRange (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range := by
  rw [←decompose a,map_sum,map_sum]
  apply Subalgebra.sum_mem
  intro ij _
  rw [map_smul,map_smul]
  apply Subalgebra.smul_mem
  rcases ij with ⟨⟨i,k⟩,⟨j,l⟩⟩
  rw [←matrixUnit_kronecker,map_mul,map_mul,conj_K_left_left,conj_K_left_right]
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
lemma H_cross_mem (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix a) ∈
      tensorRange (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range := by
  rw [←decompose a,map_sum,map_sum]
  apply Subalgebra.sum_mem
  intro ij _
  rw [map_smul,map_smul]
  apply Subalgebra.smul_mem
  rcases ij with ⟨⟨i,k⟩,⟨j,l⟩⟩
  rw [←matrixUnit_kronecker,map_mul,map_mul,conj_H_left_left,conj_H_left_right,
    (legs_commute _ _).symm.eq]
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩
end KirchbergRordam.FourLegSymmetries


end

end OAI
