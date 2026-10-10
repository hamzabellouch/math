import Mathlib

namespace OAI
noncomputable section
open scoped ZeroAtInfty
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def Radial {F : Type*} (f : V → F) : Prop :=
  ∀ R : V ≃ₗᵢ[ℝ] V, ∀ x, f (R x)=f x

def RealValued (f : V → ℂ) : Prop := ∀ x, star (f x)=f x
end FlatSimilarity

end

end OAI
