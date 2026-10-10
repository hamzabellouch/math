import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedCutAction
import OAI.Combinatorics.Chromatic.QuantumTorus.PureCutTelescoping

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

lemma complementAlpha_neg_p (m : k.ker) :
    complementAlpha k (-p) Ω m= -complementAlpha k p Ω m := by
  change Ω (-p) m= -Ω p m
  simp

def reciprocalFiber : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+*
    FiberTorus v (complementOmega k Ω) (complementAlpha k (-p) Ω) :=
  fiberReciprocal v (complementOmega k Ω) (complementAlpha k p Ω)
    (complementAlpha k (-p) Ω) (complementAlpha_neg_p Ω k p)

def expandFiberInfinity : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+*
    HahnSeries ℤ (Torus v Ω) :=
  (expandFiber v Ω hΩ k (-p)).comp (reciprocalFiber v Ω k p)

lemma completed_expand_opposite_inverse
    (hq : ∀n : ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0)
    (f : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))) :
    PowerSeries.map (expandFiberInfinity v Ω hΩ k p)
      (completedOppositeInverseAction v _ _ f)=
    innerHom (completedPureUnit v Ω hΩ (-p))⁻¹
      (PowerSeries.map (expandFiberInfinity v Ω hΩ k p) f) := by
  calc
    _=PowerSeries.map (expandFiber v Ω hΩ k (-p))
        ((completedPureAction v (complementOmega k Ω) (complementAlpha k (-p) Ω)).symm
          (PowerSeries.map (reciprocalFiber v Ω k p) f)) := by
      rw [completedOppositeInverseAction_eq]
      apply PowerSeries.ext
      intro d
      change expandFiber v Ω hΩ k (-p)
        (reciprocalFiber v Ω k p (oppositeInverseActionHom v _ _ (coeff d f)))=
        expandFiber v Ω hΩ k (-p)
          (pureActionInvHom v _ _ (reciprocalFiber v Ω k p (coeff d f)))
      exact congrArg (expandFiber v Ω hΩ k (-p))
        (fiberReciprocal_oppositeInverse v (complementOmega k Ω) (complementAlpha k p Ω)
          (complementAlpha k (-p) Ω) (complementAlpha_neg_p Ω k p) (coeff d f))
    _=innerHom (completedPureUnit v Ω hΩ (-p))⁻¹
        (PowerSeries.map (expandFiber v Ω hΩ k (-p))
          (PowerSeries.map (reciprocalFiber v Ω k p) f)) :=
      completed_expand_pure_inverse v Ω hΩ k (-p) hq _
    _=_ := by
      congr 1
end
end ElementaryPositivity.RationalFiber

end

end OAI
