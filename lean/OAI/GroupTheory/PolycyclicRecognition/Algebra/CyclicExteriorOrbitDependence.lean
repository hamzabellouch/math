import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicRegularExteriorObstruction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.FiniteType
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Noetherian.Basic

namespace OAI

/-! # Finite exterior square excludes a free cyclic orbit over a field -/

noncomputable section
namespace PolycyclicRecognition
variable {K : Type} [Field K]
open scoped MonoidAlgebra
variable {M P : Type} [AddCommGroup M] [Module K M] [AddCommGroup P] [Module K P]

def rationalExteriorSquareRepresentation (ρ : Representation K (Multiplicative ℤ) M) :
    Representation K (Multiplicative ℤ) (⋀[K]^2 M) where
  toFun g := exteriorPower.map 2 (ρ g)
  map_one' := by rw [map_one]; exact exteriorPower.map_id
  map_mul' g h := by rw [map_mul]; exact exteriorPower.map_comp _ _

theorem rationalExteriorMap_injective (f : M →ₗ[K] P) (hf : Function.Injective f) :
    Function.Injective (exteriorPower.map 2 f) := by
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have hi : (exteriorPower.map 2 g).comp (exteriorPower.map 2 f) = LinearMap.id := by
    rw [← exteriorPower.map_comp, hg, exteriorPower.map_id]
  apply Function.LeftInverse.injective (g := exteriorPower.map 2 g)
  intro x
  exact LinearMap.congr_fun hi x

theorem rationalExterior_finite_of_injection
    (ρ : Representation K (Multiplicative ℤ) M)
    (σ : Representation K (Multiplicative ℤ) P)
    (f : M →ₗ[K] P) (hf : Function.Injective f)
    (he : ∀ g, f.comp (ρ g) = (σ g).comp f)
    [Module.Finite K[Multiplicative ℤ] (rationalExteriorSquareRepresentation σ).asModule] :
    Module.Finite K[Multiplicative ℤ] (rationalExteriorSquareRepresentation ρ).asModule := by
  let : IsNoetherianRing K[Multiplicative ℤ] :=
    Algebra.FiniteType.isNoetherianRing K K[Multiplicative ℤ]
  let : IsNoetherian K[Multiplicative ℤ] (rationalExteriorSquareRepresentation σ).asModule :=
    isNoetherian_of_isNoetherianRing_of_finite K[Multiplicative ℤ]
      (rationalExteriorSquareRepresentation σ).asModule
  let F : Representation.IntertwiningMap (rationalExteriorSquareRepresentation ρ)
      (rationalExteriorSquareRepresentation σ) :=
    ⟨exteriorPower.map 2 f, fun g => by
      change (exteriorPower.map 2 f).comp (exteriorPower.map 2 (ρ g)) =
        (exteriorPower.map 2 (σ g)).comp (exteriorPower.map 2 f)
      rw [← exteriorPower.map_comp, ← exteriorPower.map_comp, he]⟩
  let FM : (rationalExteriorSquareRepresentation ρ).asModule →ₗ[K[Multiplicative ℤ]]
      (rationalExteriorSquareRepresentation σ).asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
    (rationalExteriorSquareRepresentation ρ) (rationalExteriorSquareRepresentation σ) F
  apply Module.Finite.of_injective FM
  intro x y hxy
  apply (rationalExteriorSquareRepresentation ρ).asModuleEquiv.injective
  apply rationalExteriorMap_injective f hf
  exact congrArg (rationalExteriorSquareRepresentation σ).asModuleEquiv hxy

def cyclicOrbitLinearMap (ρ : Representation K (Multiplicative ℤ) M) (v : M) :
    (CyclicOrbitModule (K := K)) →ₗ[K] M :=
  Finsupp.linearCombination K (fun i : ℤ => ρ (Multiplicative.ofAdd i) v)

theorem cyclicOrbitLinearMap_equivariant
    (ρ : Representation K (Multiplicative ℤ) M) (v : M) (g : Multiplicative ℤ) :
    (cyclicOrbitLinearMap ρ v).comp (cyclicShiftRepresentation g) =
      (ρ g).comp (cyclicOrbitLinearMap ρ v) := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro c
  change cyclicOrbitLinearMap ρ v (cyclicShiftRepresentation g (Finsupp.single i c)) =
    ρ g (cyclicOrbitLinearMap ρ v (Finsupp.single i c))
  rw [cyclicShiftRepresentation_single]
  simp only [cyclicOrbitLinearMap, Finsupp.linearCombination_single, map_smul]
  apply congrArg (fun w : M => c • w)
  change ρ (g * Multiplicative.ofAdd i) v = ρ g (ρ (Multiplicative.ofAdd i) v)
  rw [map_mul, Module.End.mul_apply]

theorem cyclic_orbit_dependent_of_finite_exterior
    (ρ : Representation K (Multiplicative ℤ) M)
    [Module.Finite K[Multiplicative ℤ] (rationalExteriorSquareRepresentation ρ).asModule]
    (v : M) : ¬LinearIndependent K (fun i : ℤ => ρ (Multiplicative.ofAdd i) v) := by
  intro hfree
  have hi : Function.Injective (cyclicOrbitLinearMap ρ v) := hfree
  have hfinite : Module.Finite K[Multiplicative ℤ]
      (rationalExteriorSquareRepresentation (cyclicShiftRepresentation (K := K))).asModule :=
    rationalExterior_finite_of_injection (cyclicShiftRepresentation (K := K)) ρ
      (cyclicOrbitLinearMap ρ v) hi (cyclicOrbitLinearMap_equivariant ρ v)
  exact rationalCyclicExterior_not_finite (K := K) hfinite

end PolycyclicRecognition

end

end OAI
