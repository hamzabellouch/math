import OAI.GroupTheory.PolycyclicRecognition.Analysis.ExteriorShiftIntegrality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialOrbitExterior

namespace OAI

/-! # Commuting scalar-difference operators on an exterior representation -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra Polynomial
variable {K Q M : Type} [Field K] [CommGroup Q] [AddCommGroup M] [Module K M]

local instance representationEndRing (ρ : Representation K Q M) :
    Ring (Module.End K[Q] ρ.asModule) := Module.End.instRing (R := K[Q]) (N₁ := ρ.asModule)

def intertwiningEndForget (ρ : Representation K Q M) :
    Representation.IntertwiningMap ρ ρ →ₐ[K] Module.End K M where
  toFun f := f.toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def representationEndForget (ρ : Representation K Q M) :
    Module.End K[Q] ρ.asModule →ₐ[K] Module.End K M :=
  (intertwiningEndForget ρ).comp (Representation.IntertwiningMap.equivAlgEnd ρ).symm.toAlgHom

def exteriorScalarDifference (ρ : Representation K Q M) (n : ℕ) (g : Q) (c : K) :
    Module.End K (⋀[K]^n M) := exteriorPower.map n (c • LinearMap.id - ρ g)

theorem exteriorScalarDifference_intertwines (ρ : Representation K Q M)
    (n : ℕ) (g q : Q) (c : K) :
    (exteriorScalarDifference ρ n g c).comp (higherExteriorRepresentation ρ n q) =
      (higherExteriorRepresentation ρ n q).comp (exteriorScalarDifference ρ n g c) := by
  have hc : (ρ g).comp (ρ q) = (ρ q).comp (ρ g) := by
    calc
      _ = ρ (g * q) := (map_mul ρ g q).symm
      _ = ρ (q * g) := congrArg ρ (mul_comm g q)
      _ = _ := map_mul ρ q g
  have hs : (c • LinearMap.id - ρ g).comp (ρ q) =
      (ρ q).comp (c • LinearMap.id - ρ g) := by
    ext x
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul] using
      congrArg (fun y => c • ρ q x - y) (LinearMap.congr_fun hc x)
  change (exteriorPower.map n (c • LinearMap.id - ρ g)).comp
      (exteriorPower.map n (ρ q)) = _
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_comp]
  rfl

def exteriorScalarDifferenceIntertwining (ρ : Representation K Q M) (n : ℕ) (g : Q) (c : K) :
    Representation.IntertwiningMap (higherExteriorRepresentation ρ n)
      (higherExteriorRepresentation ρ n) :=
  ⟨exteriorScalarDifference ρ n g c, fun q => exteriorScalarDifference_intertwines ρ n g q c⟩

def exteriorScalarDifferenceModule (ρ : Representation K Q M) (n : ℕ) (g : Q) (c : K) :
    Module.End K[Q] (higherExteriorRepresentation ρ n).asModule :=
  Representation.IntertwiningMap.equivAlgEnd _ (exteriorScalarDifferenceIntertwining ρ n g c)

@[simp] theorem representationEndForget_difference (ρ : Representation K Q M)
    (n : ℕ) (g : Q) (c : K) :
    representationEndForget (higherExteriorRepresentation ρ n)
      (exteriorScalarDifferenceModule ρ n g c) = exteriorScalarDifference ρ n g c := by
  simp only [representationEndForget, exteriorScalarDifferenceModule, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  rfl

theorem exteriorScalarDifferenceModule_commute (ρ : Representation K Q M)
    (n : ℕ) (g : Q) (c d : K) :
    Commute (exteriorScalarDifferenceModule ρ n g c)
      (exteriorScalarDifferenceModule ρ n g d) := by
  have hs : (c • LinearMap.id - ρ g).comp (d • LinearMap.id - ρ g) =
      (d • LinearMap.id - ρ g).comp (c • LinearMap.id - ρ g) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul, smul_sub, smul_smul]
    rw [mul_comm c d]
    abel
  have he : (exteriorScalarDifference ρ n g c) * (exteriorScalarDifference ρ n g d) =
      (exteriorScalarDifference ρ n g d) * (exteriorScalarDifference ρ n g c) := by
    change (exteriorPower.map n _).comp (exteriorPower.map n _) = _
    rw [← exteriorPower.map_comp, hs, exteriorPower.map_comp]
    rfl
  apply (Representation.IntertwiningMap.equivAlgEnd _).symm.injective
  apply Representation.IntertwiningMap.toLinearMap_injective
  exact he

theorem polynomialOrbitExterior_scalarDifference (T : Module.End K M) (v : M)
    (n : ℕ) (c : K) :
    (exteriorPower.map n (polynomialOrbitMap T v)).comp
        (exteriorPower.map n (LinearMap.mulLeft K (Polynomial.C c - Polynomial.X))) =
      (exteriorPower.map n (c • LinearMap.id - T)).comp
        (exteriorPower.map n (polynomialOrbitMap T v)) := by
  have he : (polynomialOrbitMap T v).comp
      (LinearMap.mulLeft K (Polynomial.C c - Polynomial.X)) =
      (c • LinearMap.id - T).comp (polynomialOrbitMap T v) := by
    apply LinearMap.ext
    intro p
    change polynomialOrbitMap T v ((Polynomial.C c - Polynomial.X) * p) = _
    rw [polynomialOrbitMap_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rfl
  rw [← exteriorPower.map_comp, he, exteriorPower.map_comp]

end PolycyclicRecognition

end

end OAI
