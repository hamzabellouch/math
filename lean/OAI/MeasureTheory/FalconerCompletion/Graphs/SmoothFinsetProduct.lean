import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularOperator

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open scoped ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [DecidableEq ι]

noncomputable def smoothFinsetProductND (S : Finset ι) (f : ι → SmoothFunctionND V) : SmoothFunctionND V :=
  ⟨fun x => ∏ i ∈ S, (f i).1 x,contDiff_prod (fun i _ => smoothFunctionND_contDiff (f i))⟩

lemma angularOperatorND_finset_product (A : V →L[ℝ] V) (S : Finset ι) (f : ι → SmoothFunctionND V) :
    angularOperatorND A (smoothFinsetProductND S f)=
      ∑ i ∈ S, smoothFinsetProductND S (Function.update f i (angularOperatorND A (f i))) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun x => ∏ i ∈ S, (f i).1 x) x (A x) = _
  rw [fderiv_finsetProd (fun i _ => (smoothFunctionND_contDiff (f i)).differentiable (by simp) x)]
  simp only [sum_apply,smul_apply,smul_eq_mul,
    Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change _ = ∏ j ∈ S, (Function.update f i (angularOperatorND A (f i)) j).1 x
  have he : (fun j => (Function.update f i (angularOperatorND A (f i)) j).1 x)=
      Function.update (fun j => (f j).1 x) i (angularDerivativeND A (f i).1 x) := by
    funext j
    by_cases hj : j=i <;> simp [hj,angularOperatorND]
  rw [he,Finset.prod_update_of_mem hi,Finset.sdiff_singleton_eq_erase]
  simp only [angularDerivativeND]
  ring

noncomputable def orderedAngularAssignmentsND (S : Finset ι) :
    List (V →L[ℝ] V) → List (ι → List (V →L[ℝ] V))
  | [] => [fun _ => []]
  | A::L => (orderedAngularAssignmentsND S L).flatMap
      (fun k => S.toList.map (fun i => Function.update k i (A::k i)))

lemma orderedAngularAssignmentsND_length (S : Finset ι) (L : List (V →L[ℝ] V)) :
    (orderedAngularAssignmentsND S L).length=S.card^L.length := by
  induction L with
  | nil => simp [orderedAngularAssignmentsND]
  | cons A L ih => simp [orderedAngularAssignmentsND,List.length_flatMap,ih,pow_succ]

lemma orderedAngularAssignmentsND_budget (S : Finset ι) (L : List (V →L[ℝ] V))
    {k : ι → List (V →L[ℝ] V)} (hk : k ∈ orderedAngularAssignmentsND S L) :
    ∑ i ∈ S, (k i).length=L.length := by
  induction L generalizing k with
  | nil => simp only [orderedAngularAssignmentsND,List.mem_singleton] at hk; subst k; simp
  | cons A L ih =>
    obtain ⟨l,hl,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    have hi : i ∈ S := Finset.mem_toList.mp hi
    have he : (fun j => (Function.update l i (A::l i) j).length)=
        Function.update (fun j => (l j).length) i ((l i).length+1) := by
      funext j
      by_cases hj : j=i <;> simp [hj]
    rw [he,Finset.sum_update_of_mem hi,Finset.sdiff_singleton_eq_erase]
    have hh := Finset.add_sum_erase S (fun i => (l i).length) hi
    rw [ih hl] at hh
    simp only [List.length_cons]
    omega

lemma angularWordOperatorND_ordered_product (S : Finset ι) (f : ι → SmoothFunctionND V)
    (L : List (V →L[ℝ] V)) :
    angularWordOperatorND L (smoothFinsetProductND S f)=
      ((orderedAngularAssignmentsND S L).map (fun k =>
        smoothFinsetProductND S (fun i => angularWordOperatorND (k i) (f i)))).sum := by
  induction L with
  | nil => simp [angularWordOperatorND,orderedAngularAssignmentsND]
  | cons A L ih =>
    change angularOperatorND A (angularWordOperatorND L (smoothFinsetProductND S f)) = _
    rw [ih,map_list_sum]
    simp only [List.map_map,Function.comp_def,orderedAngularAssignmentsND,
      List.flatMap_def,List.map_flatten,List.sum_flatten]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [angularOperatorND_finset_product]
    rw [← List.sum_toFinset _ S.nodup_toList]
    rw [Finset.toList_toFinset]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext j
    by_cases hj : j=i <;> simp [hj,angularWordOperatorND,Module.End.mul_apply]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
