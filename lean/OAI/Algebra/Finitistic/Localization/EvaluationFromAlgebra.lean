import OAI.Algebra.Finitistic.Localization.EvaluationModule
import Mathlib.Algebra.Algebra.Tower

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {R : Type v} [Ring R] [Algebra k R]

/-- The displayed finite list of quadratic equations, in an arbitrary k-algebra. -/
def Relations.Satisfies (x : Fin d → R) : Prop := ∀ j,
  (∑ h, ∑ l, P.quadratic j h l • (x h * x l)) +
    (∑ h, P.linear j h • x h) + P.constant j • (1 : R) = 0

namespace Representation
variable {P} {Y : Type w} [AddCommGroup Y] [Module k Y]

/-- Evaluate the quadratic presentation in any actual algebra action. -/
def ofAction (x : Fin d → R) (hx : P.Satisfies x) (ρ : R →ₐ[k] Module.End k Y) :
    Representation P Y where
  generator h := ρ (x h)
  relation j := by
    have h := congrArg ρ (hx j)
    simpa only [map_add, map_sum, map_smul, map_mul, map_one, map_zero] using h

/-- In particular, every R-module supplies the required representation. -/
def ofModule (x : Fin d → R) (hx : P.Satisfies x)
    [Module R Y] [IsScalarTower k R Y] : Representation P Y :=
  ofAction x hx (Algebra.lsmul k k Y)

@[simp] theorem ofModule_generator (x : Fin d → R) (hx : P.Satisfies x)
    [Module R Y] [IsScalarTower k R Y] (h : Fin d) (y : Y) :
    (ofModule (Y := Y) x hx).generator h y = x h • y := rfl
end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
