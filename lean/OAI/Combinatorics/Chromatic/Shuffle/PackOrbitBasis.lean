import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GradeBInternal
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogeneousBasisFibre
import OAI.Combinatorics.Chromatic.Shuffle.PackExponentSorting
import OAI.Combinatorics.Chromatic.Walls.FiniteFibreFinsupp

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.ShufflePolynomiality
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma packSymmetric_coeff_permute (d : I → ℕ) (f : S d)
    (g : ∀ i,Equiv.Perm (Fin (d i))) (m : PackExponent d) :
    f.val.coeff (m.mapDomain (packAction (fun i=>Fin (d i)) g))=f.val.coeff m := by
  have H:=coeff_rename_mapDomain _ (packAction (fun i=>Fin (d i)) g).injective f.val m
  rw [f.property g] at H
  exact H

omit [DecidableEq I] in
lemma packSymmetric_coeff_sorted (d : I → ℕ) (f : S d) (m : PackExponent d) :
    f.val.coeff m=f.val.coeff (sortedPackRepresentative d (sortPackExponent d m)) := by
  have h:=packSymmetric_coeff_permute d f (fun i=>Tuple.sort (fun j=>m ⟨i,j⟩))
    (sortedPackRepresentative d (sortPackExponent d m))
  rwa [packExponent_of_sorted] at h

omit [DecidableEq I] in
lemma packSymmetric_iff_fibre (d : I → ℕ) (f : MvPolynomial (Σ i,Fin (d i)) ℚ) :
    PackSymmetric d f ↔ AddMonoidAlgebra.coeff f∈fibreConstant (sortPackExponent d) := by
  constructor
  · intro hf m n h
    change f.coeff m=f.coeff n
    rw [packSymmetric_coeff_sorted d ⟨f,hf⟩ m,packSymmetric_coeff_sorted d ⟨f,hf⟩ n,h]
  · intro hf g
    ext m
    have H:=coeff_rename_mapDomain (packAction (fun i=>Fin (d i)) g)
      (packAction (fun i=>Fin (d i)) g).injective f
      (m.mapDomain (packAction (fun i=>Fin (d i)) (fun i=>(g i).symm)))
    rw [packExponent_permute_inverse] at H
    exact H.trans (hf _ _ (sortPack_permute d _ m))

noncomputable def packFibreEquiv (d : I → ℕ) :
    fibreConstant (sortPackExponent d) ≃ₗ[ℚ] S d where
  toFun f := ⟨AddMonoidAlgebra.ofCoeff f.val,(packSymmetric_iff_fibre d (AddMonoidAlgebra.ofCoeff f.val)).mpr f.property⟩
  invFun f := ⟨AddMonoidAlgebra.coeff f.val,(packSymmetric_iff_fibre d f.val).mp f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def packOrbitBasis (d : I → ℕ) : Module.Basis (SortedPackExponent d) ℚ (S d) :=
  (fibreConstantBasis (sortPackExponent d) (sortPack_fibre_finite d)
    (sortedPackRepresentative d) (sortPack_representative d)).map (packFibreEquiv d)

omit [DecidableEq I] in
lemma packOrbitBasis_coeff (d : I → ℕ) (k : SortedPackExponent d) (m : PackExponent d) :
    (packOrbitBasis d k).val.coeff m=if sortPackExponent d m=k then 1 else 0 := by
  have H:=fibreConstantBasis_apply (sortPackExponent d) (sortPack_fibre_finite d)
    (sortedPackRepresentative d) (sortPack_representative d) k m
  by_cases h : sortPackExponent d m=k
  · simp only [ite_eq_left h] at H ⊢; exact H
  · simp only [ite_eq_right h] at H ⊢; exact H

noncomputable def sortedPackDegree (d : I → ℕ) (k : SortedPackExponent d) : ℕ :=
  ∑ i,∑ j,(k i).val j

omit [DecidableEq I] in
lemma packExponent_degree_sort (d : I → ℕ) (m : PackExponent d) :
    sortedPackDegree d (sortPackExponent d m)=m.sum (fun _ n=>n) := by
  unfold sortedPackDegree sortPackExponent
  simp only [Function.comp_apply]
  calc
    _ = ∑ i,∑ j,m ⟨i,j⟩ := Finset.sum_congr rfl (fun i _=> Equiv.sum_comp (Tuple.sort (fun j=>m ⟨i,j⟩)) (fun j=>m ⟨i,j⟩))
    _ = ∑ ij,m ij := (Fintype.sum_sigma _).symm
    _ = _ := (m.sum_fintype (fun _ n=>n) (fun _=>rfl)).symm

omit [DecidableEq I] in
lemma packOrbitBasis_homogeneous (d : I → ℕ) (k : SortedPackExponent d) :
    (packOrbitBasis d k).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) (sortedPackDegree d k) := by
  intro m hm
  have h : sortPackExponent d m=k := by
    by_contra h
    rw [packOrbitBasis_coeff,ite_eq_right h] at hm
    exact hm rfl
  rw [←h,packExponent_degree_sort]
  simp [Finsupp.weight_apply,Finsupp.sum]

omit [DecidableEq I] in
lemma packOrbitBasis_component (d : I → ℕ) (ℓ : ℤ) (k : SortedPackExponent d) :
    componentS d ℓ (packOrbitBasis d k)=
      if (sortedPackDegree d k : ℤ)=ℓ then packOrbitBasis d k else 0 := by
  rw [componentS_of_homogeneous d _ (packOrbitBasis_homogeneous d k)]
  simp only [eq_comm]

omit [DecidableEq I] in
theorem packHilbert_coefficient (d : I → ℕ) (ℓ : ℤ) :
    Module.finrank ℚ (LinearMap.range (componentS d ℓ))=
      Nat.card {k : SortedPackExponent d // (sortedPackDegree d k : ℤ)=ℓ} := by
  let := componentS_range_finite d ℓ
  exact ElementaryPositivity.homogeneousBasis_finrank (packOrbitBasis d) _ _
    (packOrbitBasis_component d) ℓ
end ElementaryPositivity.RawShuffle

end

end OAI
