import OAI.GroupTheory.PolycyclicRecognition.Algebra.TwistedBilateralSequence
import Mathlib.RepresentationTheory.Rep.Basic

namespace OAI

/-! # The quotient action with a coefficient twist -/

noncomputable section
namespace PolycyclicRecognition

open Representation

variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

def twistedBilateralRepresentation (e : M ≃ₗ[k] M) :
    Representation k (Multiplicative ℤ) (ℤ →₀ M) where
  toFun z := (bilateralGauge k M e).symm.toLinearMap ∘ₗ
    bilateralTranslation k M z ∘ₗ (bilateralGauge k M e).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro f
    simp
  map_mul' x y := by
    apply LinearMap.ext
    intro f
    simp [Module.End.mul_apply]

theorem twistedBilateralRepresentation_generator (e : M ≃ₗ[k] M) (f : ℤ →₀ M) :
    twistedBilateralRepresentation k M e (Multiplicative.ofAdd 1) f =
      twistedBilateralShift k M e f := by
  apply (bilateralGauge k M e).injective
  change bilateralGauge k M e
      ((bilateralGauge k M e).symm
        (bilateralTranslation k M (Multiplicative.ofAdd 1) (bilateralGauge k M e f))) = _
  rw [LinearEquiv.apply_symm_apply, bilateralGauge_shift]

def twistedBilateralRep (e : M ≃ₗ[k] M) : Rep k (Multiplicative ℤ) :=
  Rep.of (twistedBilateralRepresentation k M e)

end PolycyclicRecognition

end

end OAI
