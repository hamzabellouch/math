import OAI.Algebra.Finitistic.Localization.NativeBoundedDerived

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- Direct adapter for the boundedness and right-projectivity fields of the native fixed rectification. -/
def nativeProjectiveModel (P : BiComplex k B) (lo hi : ℤ)
    (bounded : ∀ n, n < lo ∨ hi < n → IsZero (P.X n))
    (projective : ∀ n, CategoryTheory.Projective ((right k B P).X n)) :
    BoundedProjective k B P where
  lower := lo
  upper := hi
  bounded := bounded
  projective n := by
    let := projective n
    exact inferInstanceAs (Module.Projective Bᵐᵒᵖ ((right k B P).X n))
end LittleFinitistic.BimoduleTotal

end

end OAI
