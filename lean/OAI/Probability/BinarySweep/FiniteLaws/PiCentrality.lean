import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.PiTensorMatrices
import OAI.Probability.BinarySweep.TensorBounds.SignedConjugation

namespace OAI

noncomputable section
open scoped BigOperators Classical Kronecker
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
lemma piTensorMatrices_split (i : I) (P : ∀i, Matrix (A i) (A i) ℂ) :
    piTensorMatrices P = (P i ⊗ₖ piTensorMatrices (fun j : {j // j≠i} => P j)).submatrix
      (Equiv.piSplitAt i A) (Equiv.piSplitAt i A) := by
  ext x y
  change (∏j, P j (x j) (y j)) = P i (x i) (y i) * ∏j : {j // j≠i}, P j (x j) (y j)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  exact Finset.prod_subtype (Finset.univ.erase i) (by intro j; simp [ne_comm]) _

def siteMatrix (i : I) (P : Matrix (A i) (A i) ℂ) : Matrix (∀i,A i) (∀i,A i) ℂ :=
  (P ⊗ₖ (1 : Matrix (∀j : {j // j≠i}, A j) (∀j : {j // j≠i}, A j) ℂ)).submatrix
    (Equiv.piSplitAt i A) (Equiv.piSplitAt i A)

omit [∀ i, Fintype (A i)] in
lemma siteMatrix_eq_mask (i : I) (P : ∀i, Matrix (A i) (A i) ℂ) :
    siteMatrix i (P i) = piTensorMatrices (fun j => if j=i then P j else 1) := by
  rw [piTensorMatrices_split i]
  simp only
  have he : piTensorMatrices (fun j : {j // j≠i} => if j.val=i then P j else 1)=1 := by
    have hh : (fun j : {j // j≠i} => if j.val=i then P j else 1) = (fun j : {j // j≠i} => (1 : Matrix (A j) (A j) ℂ)) := by
      funext j
      exact ite_eq_right j.property
    rw [hh]
    exact piTensorMatrices_one
  rw [he]
  rfl

lemma siteMatrix_centrality {G : Type*} (i : I) (T : G → Matrix (A i) (A i) ℂ)
    (P : Matrix (A i) (A i) ℂ)
    (hP : ∀ X : Matrix (A i) (A i) ℂ, (∀g, X*T g=T g*X) → X*P=P*X)
    (M : Matrix (∀i,A i) (∀i,A i) ℂ) (hM : ∀g, M*siteMatrix i (T g)=siteMatrix i (T g)*M) :
    M*siteMatrix i P=siteMatrix i P*M := by
  let e := Equiv.piSplitAt i A
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  have he (Q : Matrix (A i) (A i) ℂ) : E (siteMatrix i Q)=Q ⊗ₖ 1 := by
    ext x y
    change (Q ⊗ₖ 1) (e (e.symm x)) (e (e.symm y))=(Q ⊗ₖ 1) x y
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  have hc : ∀g, E M*(T g ⊗ₖ 1)=(T g ⊗ₖ 1)*E M := by
    intro g
    simpa only [map_mul,he] using congrArg E (hM g)
  apply E.injective
  simp only [map_mul,he]
  exact kronecker_centrality T P hP (E M) hc

theorem piTensor_centrality {G : I → Type*} (T : ∀ i, G i → Matrix (A i) (A i) ℂ)
    (P : ∀i, Matrix (A i) (A i) ℂ)
    (hP : ∀i, ∀X : Matrix (A i) (A i) ℂ, (∀g, X*T i g=T i g*X) → X*P i=P i*X)
    (M : Matrix (∀i,A i) (∀i,A i) ℂ)
    (hM : ∀i g, M*siteMatrix i (T i g)=siteMatrix i (T i g)*M) :
    M*piTensorMatrices P=piTensorMatrices P*M := by
  have hi (i : I) : M*siteMatrix i (P i)=siteMatrix i (P i)*M :=
    siteMatrix_centrality i (T i) (P i) (hP i) M (hM i)
  have hh (s : Finset I) : M*piTensorMatrices (fun i => if i∈s then P i else 1)=
      piTensorMatrices (fun i => if i∈s then P i else 1)*M := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty,ite_false,piTensorMatrices_one,mul_one,one_mul]
    | @insert i s his ih =>
      have he : piTensorMatrices (fun j => if j∈insert i s then P j else 1)=
          siteMatrix i (P i)*piTensorMatrices (fun j => if j∈s then P j else 1) := by
        rw [siteMatrix_eq_mask,piTensorMatrices_mul]
        congr 1
        funext j
        by_cases hji : j=i
        · subst j; simp [his]
        · simp [hji,Finset.mem_insert]
      rw [he,← mul_assoc,hi,mul_assoc,ih,← mul_assoc]
  simpa only [Finset.mem_univ,ite_true] using hh Finset.univ

end BinaryCoordinateSweeps.Density

end

end OAI
