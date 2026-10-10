import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Finite conditional seed kernels

The observation map can include the branch and the sacrificed mask. Its domain
is the *complete* source seed, so conditioning does not discard unused coins.
These definitions are independent of every proposed selection-rule proof.
-/

namespace MatroidProphet.Secretary

open scoped BigOperators

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-- The source mass of a fiber of the observation map. -/
noncomputable def fiberMass (p : α → ℝ) (f : α → β) (b : β) : ℝ :=
  ∑ a, if f a = b then p a else 0

/-- The conditional source mass, totalized by a fixed point mass on empty fibers.
The fallback only concerns observations of source probability zero. -/
noncomputable def fiberKernel (p : α → ℝ) (f : α → β) (fallback : α)
    (b : β) (a : α) : ℝ :=
  if fiberMass p f b = 0 then
    if a = fallback then 1 else 0
  else if f a = b then p a / fiberMass p f b else 0

end MatroidProphet.Secretary

end OAI
