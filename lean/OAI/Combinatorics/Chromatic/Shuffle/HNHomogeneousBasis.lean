import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNIndependent
import OAI.Combinatorics.Chromatic.Walls.Grade

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
lemma dfinsupp_basis_apply {J : Type*} [DecidableEq J] {M : J → Type*} [∀ j,AddCommGroup (M j)]
    [∀ j,Module ℚ (M j)] {K : J → Type*} (b : ∀ j,Module.Basis (K j) ℚ (M j))
    (j : J) (k : K j) : DFinsupp.basis b ⟨j,k⟩=DFinsupp.single j (b j k) := by
  classical
  apply Module.Basis.apply_eq_iff.mpr
  ext ⟨i,l⟩
  by_cases h : i=j
  · subst i
    simp [DFinsupp.basis,Finsupp.single_apply]
  · simp [DFinsupp.basis,h,Ne.symm h]

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

local instance gradeBFinite (d : I → ℕ) (k : ℤ) : Module.Finite ℚ (gradeB a (slope c η) d k) :=
  gradeB_finite a (slope c η) d k

local instance gradeBFree (d : I → ℕ) (k : ℤ) : Module.Free ℚ (gradeB a (slope c η) d k) :=
  Module.Free.of_divisionRing ℚ _

abbrev HomogeneousBIndex (d : I → ℕ) := Σ k : ℤ,Fin (Module.finrank ℚ (gradeB a (slope c η) d k))
noncomputable def homogeneousBBasis (d : I → ℕ) : Module.Basis (HomogeneousBIndex a c η d) ℚ (B a (slope c η) d) :=
  (gradeB_internal a (slope c η) d).collectedBasis (fun k=>Module.finBasis ℚ (gradeB a (slope c η) d k))
lemma homogeneousBBasis_mem (d : I → ℕ) (i : HomogeneousBIndex a c η d) :
    homogeneousBBasis a c η d i∈gradeB a (slope c η) d i.1 :=
  (gradeB_internal a (slope c η) d).collectedBasis_mem _ i

def HNBasisIndex : List (I → ℕ) → Type
  | [] => Unit
  | d::l => HomogeneousBIndex a c η d × HNBasisIndex l
noncomputable def hnTensorBasis : (l : List (I → ℕ)) → Module.Basis (HNBasisIndex a c η l) ℚ (HNTensor a c η l)
  | [] => (Module.Basis.singleton Unit ℚ).map (zeroPolynomialEquiv (I:=I)).symm
  | d::l => (homogeneousBBasis a c η d).tensorProduct (hnTensorBasis l)

def hnBasisDegree : (l : List (I → ℕ)) → HNBasisIndex a c η l → ℤ
  | [],_ => 0
  | d::l,i => i.1.1+hnBasisDegree l i.2-eulerForm a d l.sum

lemma hnTensorBasis_nil (i : Unit) : hnTensorBasis a c η [] i=(1 : S (0 : I → ℕ)) := by
  change ((Module.Basis.singleton Unit ℚ).map (zeroPolynomialEquiv (I:=I)).symm) i=_
  rw [Module.Basis.map_apply,Module.Basis.singleton_apply]
  exact one_smul ℚ (1 : S (0 : I → ℕ))
lemma hnTensorBasis_cons (d : I → ℕ) (l : List (I → ℕ))
    (i : HomogeneousBIndex a c η d) (j : HNBasisIndex a c η l) :
    hnTensorBasis a c η (d::l) (i,j)=homogeneousBBasis a c η d i⊗ₜ[ℚ]hnTensorBasis a c η l j :=
  Module.Basis.tensorProduct_apply _ _ i j

lemma hnTensorBasis_polynomial (l : List (I → ℕ)) (i : HNBasisIndex a c η l) :
    (hnPolynomial a c η (homogeneousSection a (slope c η)) l (hnTensorBasis a c η l i)).val.IsWeightedHomogeneous
      (fun _=>(1:ℤ)) (hnBasisDegree a c η l i) := by
  induction l with
  | nil =>
    have H := hnTensorBasis_nil a c η i
    exact (congrArg (fun f : S (0 : I → ℕ)=>f.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) 0) H).mpr
      (MvPolynomial.isWeightedHomogeneous_one ℚ (fun _=>(1:ℤ)))
  | cons d l ih =>
    rcases i with ⟨i,j⟩
    have H := congrArg (hnPolynomial a c η (homogeneousSection a (slope c η)) (d::l))
      (hnTensorBasis_cons a c η d l i j)
    have H' := H.trans (hnPolynomial_cons a c η (homogeneousSection a (slope c η)) d l _ _)
    exact (congrArg (fun f : S (d+l.sum)=>f.val.IsWeightedHomogeneous (fun _=>(1:ℤ))
      (i.1+hnBasisDegree a c η l j-eulerForm a d l.sum)) H').mpr
      (shufflePolynomial_homogeneous a _ _
      (homogeneousSection_graded a (slope c η) d i.1 _ (homogeneousBBasis_mem a c η d i)) (ih j))

noncomputable def hnHomogeneousBasis (hc : ∀ i,0<c i) (d : I → ℕ) :
    Module.Basis (Σ l : HNIndex c η d,HNBasisIndex a c η l.val) ℚ (S d) :=
  (DFinsupp.basis (fun l : HNIndex c η d=>hnTensorBasis a c η l.val)).map
    (hnOrderedEquiv a c η hc (homogeneousSection a (slope c η))
      (homogeneousSection_rightInverse a (slope c η)) d)

lemma hnHomogeneousBasis_apply (hc : ∀ i,0<c i) (d : I → ℕ)
    (i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val) :
    hnHomogeneousBasis a c η hc d i=dimensionCast i.1.property.1
      (hnPolynomial a c η (homogeneousSection a (slope c η)) i.1.val (hnTensorBasis a c η i.1.val i.2)) := by
  rcases i with ⟨l,i⟩
  simp only [hnHomogeneousBasis,Module.Basis.map_apply,dfinsupp_basis_apply]
  simp only [hnOrderedEquiv,LinearEquiv.ofBijective_apply,hnPolynomialExpansion,DirectSum.toModule]
  exact DFinsupp.sumAddHom_single _ _ _

lemma hnHomogeneousBasis_degree (hc : ∀ i,0<c i) (d : I → ℕ)
    (i : Σ l : HNIndex c η d,HNBasisIndex a c η l.val) :
    (hnHomogeneousBasis a c η hc d i).val.IsWeightedHomogeneous (fun _=>(1:ℤ))
      (hnBasisDegree a c η i.1.val i.2) := by
  rw [hnHomogeneousBasis_apply]
  have H := hnTensorBasis_polynomial a c η i.1.val i.2
  generalize hp : hnPolynomial a c η (homogeneousSection a (slope c η)) i.1.val
    (hnTensorBasis a c η i.1.val i.2)=x at H ⊢
  rcases i with ⟨⟨l,hl,ho⟩,i⟩
  dsimp only at *
  subst d
  exact H
end ElementaryPositivity.RawShuffle

end

end OAI
