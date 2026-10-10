import Mathlib.Algebra.Category.ModuleCat.Algebra

namespace OAI

open CategoryTheory
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

theorem moduleCatLinear_coherence : ModuleCat.linearOverField (k := k) (A := R) =
    ModuleCat.Algebra.instLinear (S₀ := k) (S := R) := rfl

end ArExplicit

end OAI
