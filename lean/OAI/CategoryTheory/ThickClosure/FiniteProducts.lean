import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
namespace HahnWilson.FiniteTower
variable (R : Type u) [Ring R] (D : ℕ)
theorem chainComplexFiniteProducts : HasFiniteProducts (ChainComplex (ModuleCat.{u} R) (ZMod D)) := by
  constructor
  intro n
  let : HasLimitsOfShape (Discrete (Fin n)) (ModuleCat.{u} R) :=
    ModuleCat.hasLimitsOfShape.{0,0,u,u}
  exact HomologicalComplex.instHasLimitsOfShape

end HahnWilson.FiniteTower

end

end OAI
