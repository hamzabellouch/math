import Mathlib
import OAI.Analysis.AffineBernstein.GaussCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section SigmaNormalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The genuine adjoint equivalence of a transverse linear normalization. -/
def adjointEquiv (A : E ≃L[ℝ] E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse' A.toContinuousLinearMap.adjoint
    A.symm.toContinuousLinearMap.adjoint
    (by rw [← ContinuousLinearMap.adjoint_comp];
        have h : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id])
    (by rw [← ContinuousLinearMap.adjoint_comp];
        have h : A.toContinuousLinearMap.comp A.symm.toContinuousLinearMap =
            ContinuousLinearMap.id ℝ E := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id])

lemma homogeneousSupport_linear_image (A : E ≃L[ℝ] E) (K : Set E) (e : E) :
    homogeneousSupport (A '' K) e = homogeneousSupport K (adjointEquiv A e) := by
  unfold homogeneousSupport supportValue
  congr 1
  rw [Set.image_image]
  congr 1
  funext y
  exact (ContinuousLinearMap.adjoint_inner_left A.toContinuousLinearMap y e).symm

lemma adjointEquiv_inv_apply (A : E ≃L[ℝ] E) (e : E) :
    adjointEquiv A (adjointEquiv A.symm e) = e := by
  change (A.toContinuousLinearMap.adjoint.comp A.symm.toContinuousLinearMap.adjoint) e = e
  rw [← ContinuousLinearMap.adjoint_comp]
  have h : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by ext x; simp
  rw [h,ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply]

omit [CompleteSpace E] in
lemma prod_image_fiber {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (B : S ≃L[ℝ] S) (A : E ≃L[ℝ] E) (C : Set (S × E)) (s : S) :
    {y | (s,y) ∈ (B.prodCongr A) '' C} = A '' {y | (B.symm s,y) ∈ C} := by
  ext y
  constructor
  · rintro ⟨⟨t,z⟩,hz,he⟩
    have ht : B t = s := congrArg Prod.fst he
    have hy : A z = y := congrArg Prod.snd he
    refine ⟨z,?_,hy⟩
    simpa only [Set.mem_ofPred_eq,← ht,B.symm_apply_apply] using hz
  · rintro ⟨z,hz,rfl⟩
    exact ⟨(B.symm s,z),hz,by simp⟩

/- The support of the actual normalized fiber, pulled back by inverse-adjoint
normal variables, is the original support. No fiber hypothesis is used. -/
lemma support_normalized_pullback {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (B : S ≃L[ℝ] S) (A : E ≃L[ℝ] E) (C : Set (S × E)) :
    (fun q : S × E => homogeneousSupport {y | (B q.1,y) ∈ (B.prodCongr A) '' C}
      (adjointEquiv A.symm q.2)) =
    (fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ C} q.2) := by
  funext q
  rw [prod_image_fiber,homogeneousSupport_linear_image,adjointEquiv_inv_apply,B.symm_apply_apply]
end SigmaNormalization


end DependencyScope


end AffineBernstein
end

end OAI
