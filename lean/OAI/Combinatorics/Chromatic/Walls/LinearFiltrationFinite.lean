import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationInterchange

namespace OAI

section
namespace ElementaryPositivity.LinearFiltration
variable {M : Type*} [AddCommGroup M] [Module ℚ M]

lemma map_range_finite (F F' : Submodule ℚ M) (f : Module.End ℚ M)
    (h : ∀ x∈F,f x∈F) (h' : ∀ x∈F',f x∈F')
    [Module.Finite ℚ (LinearMap.range f)] :
    Module.Finite ℚ (LinearMap.range (map F F' F F' f h h')) := by
  let R:=LinearMap.range (restrict F F f h)
  let J : R →ₗ[ℚ] LinearMap.range f :=
    (F.subtype.comp R.subtype).codRestrict _ (by
      rintro ⟨x,⟨y,rfl⟩⟩
      exact ⟨y.val,rfl⟩)
  have hJ : Function.Injective J := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.range f => (z : M)) hxy
  let : Module.Finite ℚ R:=Module.Finite.of_injective J hJ
  let H:=map F F' F F' f h h'
  let L : R →ₗ[ℚ] LinearMap.range H :=
    ((mk F F').comp R.subtype).codRestrict _ (by
      rintro ⟨x,⟨y,rfl⟩⟩
      exact ⟨mk F F' y,rfl⟩)
  apply Module.Finite.of_surjective L
  rintro ⟨x,⟨y,rfl⟩⟩
  induction y using Submodule.Quotient.induction_on with
  | H y => exact ⟨⟨restrict F F f h y,⟨y,rfl⟩⟩,rfl⟩
end ElementaryPositivity.LinearFiltration

end

end OAI
