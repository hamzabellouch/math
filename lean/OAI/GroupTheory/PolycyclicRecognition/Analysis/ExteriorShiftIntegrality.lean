import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianNormalHigherExteriorFiniteness
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

namespace OAI

/-! # Polynomial relations for shifts on finite exterior modules

For an abelian acting group, applying a scalar shift of a group operator in
every exterior coordinate commutes with the diagonal action. If the exterior
module is finite, this operator satisfies a monic polynomial over the group ring.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {K Q M : Type} [Field K] [CommGroup Q] [AddCommGroup M] [Module K M]

def exteriorShift (ρ : Representation K Q M) (n : ℕ) (g : Q) (c : K) :
    Module.End K (⋀[K]^n M) :=
  exteriorPower.map n (ρ g - c • LinearMap.id)

theorem exteriorShift_intertwines (ρ : Representation K Q M) (n : ℕ) (g q : Q) (c : K) :
    (exteriorShift ρ n g c).comp (higherExteriorRepresentation ρ n q) =
      (higherExteriorRepresentation ρ n q).comp (exteriorShift ρ n g c) := by
  have hc : (ρ g).comp (ρ q) = (ρ q).comp (ρ g) := by
    calc
      _ = ρ (g * q) := (map_mul ρ g q).symm
      _ = ρ (q * g) := congrArg ρ (mul_comm g q)
      _ = _ := map_mul ρ q g
  have hs : (ρ g - c • LinearMap.id).comp (ρ q) =
      (ρ q).comp (ρ g - c • LinearMap.id) := by
    ext x
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul] using
      congrArg (fun y => y - c • ρ q x) (LinearMap.congr_fun hc x)
  change (exteriorPower.map n (ρ g - c • LinearMap.id)).comp
      (exteriorPower.map n (ρ q)) = _
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_comp]
  rfl

def exteriorShiftIntertwining (ρ : Representation K Q M) (n : ℕ) (g : Q) (c : K) :
    Representation.IntertwiningMap (higherExteriorRepresentation ρ n)
      (higherExteriorRepresentation ρ n) :=
  ⟨exteriorShift ρ n g c, fun q => exteriorShift_intertwines ρ n g q c⟩

def exteriorShiftModule (ρ : Representation K Q M) (n : ℕ) (g : Q) (c : K) :
    Module.End K[Q] (higherExteriorRepresentation ρ n).asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (exteriorShiftIntertwining ρ n g c)

local instance exteriorShiftEndRing (ρ : Representation K Q M) (n : ℕ) :
    Ring (Module.End K[Q] (higherExteriorRepresentation ρ n).asModule) :=
  Module.End.instRing (R := K[Q]) (N₁ := (higherExteriorRepresentation ρ n).asModule)

theorem exteriorShiftModule_integral (ρ : Representation K Q M) (n : ℕ) (g : Q) (c : K)
    [Module.Finite K[Q] (higherExteriorRepresentation ρ n).asModule] :
    IsIntegral K[Q] (exteriorShiftModule ρ n g c) := by
  let := Module.End.isIntegral (R := K[Q])
    (M := (higherExteriorRepresentation ρ n).asModule)
  exact Algebra.IsIntegral.isIntegral _

theorem exteriorShiftModule_monic_relation (ρ : Representation K Q M) (n : ℕ)
    (g : Q) (c : K) [Module.Finite K[Q] (higherExteriorRepresentation ρ n).asModule] :
    ∃ p : Polynomial K[Q], p.Monic ∧
      Polynomial.aeval (exteriorShiftModule ρ n g c) p = 0 :=
  exteriorShiftModule_integral ρ n g c

end PolycyclicRecognition

end

end OAI
