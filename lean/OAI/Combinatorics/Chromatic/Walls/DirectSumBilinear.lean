import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open scoped DirectSum
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable (M : ι → Type*) (N : κ → Type*)
variable [∀ i,AddCommGroup (M i)] [∀ i,Module ℚ (M i)]
variable [∀ j,AddCommGroup (N j)] [∀ j,Module ℚ (N j)]
variable (P : Type*) [AddCommGroup P] [Module ℚ P]

noncomputable def directSumBilinear (f : ∀ i j,M i →ₗ[ℚ] N j →ₗ[ℚ] P) :
    (⨁ i,M i) →ₗ[ℚ] (⨁ j,N j) →ₗ[ℚ] P :=
  DirectSum.toModule ℚ ι ((⨁ j,N j) →ₗ[ℚ] P) (fun i=>
    { toFun := fun x=>DirectSum.toModule ℚ κ P (fun j=>f i j x)
      map_add' := by
        intro x y
        apply DirectSum.linearMap_ext
        intro j
        ext z
        simp only [LinearMap.comp_apply,DirectSum.toModule_lof,LinearMap.add_apply,map_add]
      map_smul' := by
        intro r x
        apply DirectSum.linearMap_ext
        intro j
        ext z
        simp only [LinearMap.comp_apply,DirectSum.toModule_lof,LinearMap.smul_apply,map_smul]
        rfl })

lemma directSumBilinear_lof (f : ∀ i j,M i →ₗ[ℚ] N j →ₗ[ℚ] P)
    (i : ι) (j : κ) (x : M i) (y : N j) :
    directSumBilinear M N P f (DirectSum.lof ℚ ι M i x) (DirectSum.lof ℚ κ N j y)=f i j x y := by
  simp only [directSumBilinear,DirectSum.toModule_lof,LinearMap.coe_mk,AddHom.coe_mk]

end ElementaryPositivity

end

end OAI
