import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M N P : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  [AddCommGroup P] [Module ℚ P]

noncomputable def bilinearRestrict (F : Submodule ℚ M) (G : Submodule ℚ N) (H : Submodule ℚ P)
    (μ : M →ₗ[ℚ] N →ₗ[ℚ] P) (h : ∀ x∈F,∀ y∈G,μ x y∈H) : F →ₗ[ℚ] G →ₗ[ℚ] H where
  toFun x := restrict G H (μ x.val) (h x.val x.property)
  map_add' x y := by ext z; exact μ.map_add₂ x.val y.val z.val
  map_smul' r x := by ext z; exact μ.map_smul₂ r x.val z.val

noncomputable def bilinear (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (H H' : Submodule ℚ P) (μ : M →ₗ[ℚ] N →ₗ[ℚ] P)
    (h : ∀ x∈F,∀ y∈G,μ x y∈H)
    (hl : ∀ x∈F',∀ y∈G,μ x y∈H') (hr : ∀ x∈F,∀ y∈G',μ x y∈H') :
    Grade F F' →ₗ[ℚ] Grade G G' →ₗ[ℚ] Grade H H' := by
  let μ₀:=bilinearRestrict F G H μ h
  let L : F →ₗ[ℚ] Grade G G' →ₗ[ℚ] Grade H H' :=
    { toFun x := (next G G').liftQ ((mk H H').comp (μ₀ x)) (by
        intro y hy
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hr x.val x.property y.val hy))
      map_add' := by
        intro x y
        ext z
        induction z using Submodule.Quotient.induction_on with
        | H z => exact congrArg (mk H H') (μ₀.map_add₂ x y z)
      map_smul' := by
        intro r x
        ext z
        induction z using Submodule.Quotient.induction_on with
        | H z =>
          change mk H H' (μ₀ (r • x) z) = r • mk H H' (μ₀ x z)
          rw [μ₀.map_smul₂, map_smul] }
  exact (next F F').liftQ L (by
    intro x hx
    ext y
    induction y using Submodule.Quotient.induction_on with
    | H y => exact (Submodule.Quotient.mk_eq_zero _).mpr (hl x.val hx y.val y.property))

lemma bilinear_mk (F F' : Submodule ℚ M) (G G' : Submodule ℚ N)
    (H H' : Submodule ℚ P) (μ : M →ₗ[ℚ] N →ₗ[ℚ] P)
    (h : ∀ x∈F,∀ y∈G,μ x y∈H)
    (hl : ∀ x∈F',∀ y∈G,μ x y∈H') (hr : ∀ x∈F,∀ y∈G',μ x y∈H')
    (x : F) (y : G) :
    bilinear F F' G G' H H' μ h hl hr (mk F F' x) (mk G G' y)=
      mk H H' ⟨μ x.val y.val,h x.val x.property y.val y.property⟩ := rfl

end ElementaryPositivity.LinearFiltration

end

end OAI
