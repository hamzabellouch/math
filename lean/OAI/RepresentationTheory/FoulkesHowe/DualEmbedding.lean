import Mathlib

namespace OAI

/-!
# Transposed embeddings

A surjective intertwiner yields an injective intertwiner in the opposite
 direction when both modules carry compatible perfect pairings.  This is an
 algebraic alternative to splitting a representation by complete reducibility.
-/

noncomputable section

namespace Problem346
namespace DualEmbedding

variable {R E F E' F' : Type*} [CommSemiring R]
  [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
  [AddCommMonoid E'] [Module R E'] [AddCommMonoid F'] [Module R F']

/-- Reverse a perfect pairing when the first module is reflexive.  This turns
    the usual chart `E' ≃ Dual E` into the orientation needed by `transpose`. -/
def flipPairing [Module.IsReflexive R E] (e : E' ≃ₗ[R] Module.Dual R E) :
    E ≃ₗ[R] Module.Dual R E' :=
  (Module.evalEquiv R E).trans e.dualMap

@[simp]
theorem flipPairing_apply [Module.IsReflexive R E]
    (e : E' ≃ₗ[R] Module.Dual R E) (x : E) (y : E') :
    flipPairing e x y = e y x := rfl

/-- Transport the dual of a linear map along two perfect pairings. -/
def transpose (e : E ≃ₗ[R] Module.Dual R E')
    (f : F ≃ₗ[R] Module.Dual R F') (μ : E' →ₗ[R] F') : F →ₗ[R] E :=
  e.symm.toLinearMap.comp (μ.dualMap.comp f.toLinearMap)

@[simp]
theorem pairing_transpose (e : E ≃ₗ[R] Module.Dual R E')
    (f : F ≃ₗ[R] Module.Dual R F') (μ : E' →ₗ[R] F') (y : F) (x : E') :
    e (transpose e f μ y) x = f y (μ x) := by
  simp [transpose]

/-- Surjectivity of a map implies injectivity of its transported transpose. -/
theorem transpose_injective (e : E ≃ₗ[R] Module.Dual R E')
    (f : F ≃ₗ[R] Module.Dual R F') (μ : E' →ₗ[R] F')
    (hμ : Function.Surjective μ) : Function.Injective (transpose e f μ) := by
  exact e.symm.injective.comp ((LinearMap.dualMap_injective_of_surjective hμ).comp
    f.injective)

/-- Transposition reverses an intertwining identity, with the two adjoint
    identities expressed directly as evaluations of the perfect pairings. -/
theorem transpose_intertwines
    (e : E ≃ₗ[R] Module.Dual R E') (f : F ≃ₗ[R] Module.Dual R F')
    (μ : E' →ₗ[R] F') (A : E →ₗ[R] E) (A' : E' →ₗ[R] E')
    (B : F →ₗ[R] F) (B' : F' →ₗ[R] F')
    (he : ∀ x z, e (A x) z = e x (A' z))
    (hf : ∀ y w, f (B y) w = f y (B' w))
    (hμ : μ.comp A' = B'.comp μ) :
    A.comp (transpose e f μ) = (transpose e f μ).comp B := by
  ext y
  apply e.injective
  ext x
  change e (A (transpose e f μ y)) x = e (transpose e f μ (B y)) x
  rw [he, pairing_transpose, pairing_transpose, hf]
  exact congrArg (f y) (LinearMap.congr_fun hμ x)

/-- A family of compatible adjoint actions transports a surjective
    equivariant map into an injective equivariant map in the reverse direction.
    No group structure or finite-dimensionality is needed by this argument. -/
theorem exists_intertwining_injection_of_surjective {G : Type*}
    (e : E ≃ₗ[R] Module.Dual R E') (f : F ≃ₗ[R] Module.Dual R F')
    (A : G → E →ₗ[R] E) (B : G → F →ₗ[R] F)
    (A' : G → E' →ₗ[R] E') (B' : G → F' →ₗ[R] F')
    (he : ∀ g x z, e (A g x) z = e x (A' g z))
    (hf : ∀ g y w, f (B g y) w = f y (B' g w))
    (μ : E' →ₗ[R] F') (hμ : Function.Surjective μ)
    (hcomm : ∀ g, μ.comp (A' g) = (B' g).comp μ) :
    ∃ ι : F →ₗ[R] E, Function.Injective ι ∧
      ∀ g, (A g).comp ι = ι.comp (B g) := by
  refine ⟨transpose e f μ, transpose_injective e f μ hμ, ?_⟩
  intro g
  exact transpose_intertwines e f μ (A g) (A' g) (B g) (B' g)
    (he g) (hf g) (hcomm g)

end DualEmbedding
end Problem346

end

end OAI
