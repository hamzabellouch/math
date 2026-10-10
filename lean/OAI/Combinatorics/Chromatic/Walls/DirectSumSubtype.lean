import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open scoped DirectSum
universe u v
variable {K : Type u} [DecidableEq K] (M : K → Type v) [∀ k,AddCommGroup (M k)] [∀ k,Module ℚ (M k)]
  (p : K → Prop)
attribute [local instance] Classical.propDecidable

noncomputable def subfamilyInclusion : (⨁ k : {k // p k},M k.val) →ₗ[ℚ] ⨁ k,M k :=
  DirectSum.toModule ℚ _ _ (fun k=>DirectSum.lof ℚ K M k.val)

lemma subfamilyInclusion_lof (k : {k // p k}) (x : M k.val) :
    subfamilyInclusion M p (DirectSum.lof ℚ _ (fun k : {k // p k}=>M k.val) k x)=
      DirectSum.lof ℚ K M k.val x := by
  simp [subfamilyInclusion]

lemma component_subfamilyInclusion (k : {k // p k}) (x : ⨁ k : {k // p k},M k.val) :
    DirectSum.component ℚ K M k.val (subfamilyInclusion M p x)=
      DirectSum.component ℚ _ (fun k : {k // p k}=>M k.val) k x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of j x =>
    change DirectSum.component ℚ K M k.val (subfamilyInclusion M p
      (DirectSum.lof ℚ _ (fun k : {k // p k}=>M k.val) j x))=
      DirectSum.component ℚ _ (fun k : {k // p k}=>M k.val) k
        (DirectSum.lof ℚ _ (fun k : {k // p k}=>M k.val) j x)
    rw [subfamilyInclusion_lof]
    by_cases h : j=k
    · subst j; simp
    · rw [DirectSum.component.of,DirectSum.component.of]
      simp only [dite_eq_right (fun he=>h (Subtype.ext he)),dite_eq_right h]

lemma subfamilyInclusion_injective : Function.Injective (subfamilyInclusion M p) := by
  intro x y h
  apply DirectSum.ext_component ℚ
  intro k
  rw [←component_subfamilyInclusion M p,←component_subfamilyInclusion M p,h]

lemma directSum_map_independent {J : K → Type*} (f : ∀ k,J k → M k)
    (hf : ∀ k,LinearIndependent ℚ (f k)) {V : Type*} [AddCommGroup V] [Module ℚ V]
    (L : (⨁ k,M k) →ₗ[ℚ] V) (hL : Function.Injective L) :
    LinearIndependent ℚ (fun i : Σ k,J k=>L (DirectSum.lof ℚ K M i.1 (f i.1 i.2))) := by
  exact (DFinsupp.linearIndependent_single f hf).map' L ((LinearMap.ker_eq_bot).mpr hL)

end ElementaryPositivity

end

end OAI
