import OAI.RepresentationTheory.FoulkesHowe.PermanentPairing
import OAI.RepresentationTheory.FoulkesHowe.SymmetricLift
import OAI.RepresentationTheory.FoulkesHowe.SymmetricDual
import OAI.RepresentationTheory.FoulkesHowe.FiniteDimension
import OAI.RepresentationTheory.FoulkesHowe.Functoriality
import OAI.RepresentationTheory.FoulkesHowe.Spanning
import OAI.RepresentationTheory.FoulkesHowe.PlethysmDual

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346.PairingConstruction

universe u v
variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- Descend the right-hand family of the normalized permanent. -/
def leftMultilinear (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => X) (Module.Dual ℂ (SymPow n Y)) :=
  (symPowLiftLinear n Y ℂ).compMultilinearMap
    ((permanentPairingMultilinear n B).codRestrict
      (symmetricMultilinearSubmodule n Y ℂ) (by
        intro x σ y
        exact permanentPairingMultilinear_perm_right n B x y σ))

@[simp] theorem leftMultilinear_apply_monomial (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    leftMultilinear n B x (symMonomial n Y y) =
      permanentPairing n (fun x y => B x y) x y := by
  simp only [leftMultilinear, LinearMap.compMultilinearMap_apply,
    symPowLiftLinear_symMonomial]
  exact permanentPairingMultilinear_apply n B x y

theorem leftMultilinear_symmetric (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → X) :
    leftMultilinear n B (fun i => x (σ i)) = leftMultilinear n B x := by
  apply symPow_linearMap_ext n Y
  intro y
  simp only [leftMultilinear_apply_monomial]
  exact permanentPairing_perm_left n (fun x y => B x y) x y σ

/-- The canonical bilinear pairing induced on homogeneous symmetric powers. -/
def pairing (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    SymPow n X →ₗ[ℂ] Module.Dual ℂ (SymPow n Y) :=
  symPowLift (leftMultilinear n B) (leftMultilinear_symmetric n B)

@[simp] theorem pairing_monomials (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (x : Fin n → X) (y : Fin n → Y) :
    pairing n B (symMonomial n X x) (symMonomial n Y y) =
      permanentPairing n (fun x y => B x y) x y := by
  simp [pairing]

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- The evaluation pairing of a symmetric power and the symmetric power of its dual. -/
def dualMap (n : ℕ) :
    SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V) :=
  pairing n (LinearMap.id : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V)

@[simp] theorem dualMap_monomials (n : ℕ)
    (x : Fin n → Module.Dual ℂ V) (y : Fin n → V) :
    dualMap V n (symMonomial n (Module.Dual ℂ V) x) (symMonomial n V y) =
      permanentPairing n (fun f v => f v) x y := by
  exact pairing_monomials n LinearMap.id x y

theorem dualMap_pure (n : ℕ) (p : SymPow n (Module.Dual ℂ V)) (x : V) :
    dualMap V n p (symMonomial n V (fun _ => x)) =
      SymmetricAlgebra.lift (Module.Dual.eval ℂ V x) p.val := by
  have h : (LinearMap.applyₗ (symMonomial n V (fun _ => x))).comp (dualMap V n) =
      (SymmetricAlgebra.lift (Module.Dual.eval ℂ V x)).toLinearMap.domRestrict
        (symPowSubmodule n (Module.Dual ℂ V)) := by
    apply symPow_linearMap_ext n (Module.Dual ℂ V)
    intro f
    change dualMap V n (symMonomial n (Module.Dual ℂ V) f)
      (symMonomial n V (fun _ => x)) = _
    rw [dualMap_monomials, permanentPairing_const_right]
    simp [symMonomial, symMonomialRaw]
  exact LinearMap.congr_fun h p

theorem dualMap_injective [FiniteDimensional ℂ V] (n : ℕ) :
    Function.Injective (dualMap V n) :=
  symPowDual_injective_of_pure_evaluation V n (dualMap V n) (dualMap_pure V n)

theorem dual_finrank (n : ℕ) [FiniteDimensional ℂ V] :
    Module.finrank ℂ (SymPow n (Module.Dual ℂ V)) =
      Module.finrank ℂ (Module.Dual ℂ (SymPow n V)) := by
  rw [Subspace.dual_finrank_eq]
  let e : Module.Dual ℂ V ≃ₗ[ℂ] V :=
    LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq
  exact (symPowEquiv n e).finrank_eq

/-- Perfect duality for homogeneous symmetric powers in finite dimension. -/
def dualEquiv [FiniteDimensional ℂ V] (n : ℕ) :
    SymPow n (Module.Dual ℂ V) ≃ₗ[ℂ] Module.Dual ℂ (SymPow n V) :=
  (dualMap V n).linearEquivOfInjective (dualMap_injective V n) (dual_finrank V n)

@[simp] theorem dualEquiv_apply [FiniteDimensional ℂ V] (n : ℕ)
    (p : SymPow n (Module.Dual ℂ V)) : dualEquiv V n p = dualMap V n p := rfl

theorem dualMap_natural (n : ℕ) (f : V →ₗ[ℂ] V)
    (p : SymPow n (Module.Dual ℂ V)) (q : SymPow n V) :
    dualMap V n (symPowMap n f.dualMap p) q =
      dualMap V n p (symPowMap n f q) := by
  have h : (dualMap V n).comp (symPowMap n f.dualMap) =
      (symPowMap n f).dualMap.comp (dualMap V n) := by
    apply symPow_linearMap_ext n (Module.Dual ℂ V)
    intro x
    apply symPow_linearMap_ext n V
    intro y
    simp only [LinearMap.comp_apply, symPowMap_symMonomial,
      LinearMap.dualMap_apply, dualMap_monomials]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

theorem dualEquiv_natural [FiniteDimensional ℂ V] (n : ℕ) (f : V →ₗ[ℂ] V)
    (p : SymPow n (Module.Dual ℂ V)) (q : SymPow n V) :
    dualEquiv V n (symPowMap n f.dualMap p) q =
      dualEquiv V n p (symPowMap n f q) :=
  dualMap_natural V n f p q

/-- Canonical surjectivity on the dual space gives the equivariant comparison. -/
theorem comparison_of_surjection [FiniteDimensional ℂ V] (a b : ℕ)
    (hsurj : ∃ μ : SymPow b (SymPow a (Module.Dual ℂ V)) →ₗ[ℂ]
      SymPow a (SymPow b (Module.Dual ℂ V)),
      IsFoulkesMap a b (Module.Dual ℂ V) μ ∧ Function.Surjective μ) :
    ∃ ι : SymPow a (SymPow b V) →ₗ[ℂ] SymPow b (SymPow a V),
      IsGLEquivariantEmbedding a b V ι := by
  apply PlethysmDual.comparison_of_dual_charts a b
    (PlethysmDual.plethysmDualEquivOf b a (dualEquiv V a) (dualEquiv (SymPow a V) b))
    (PlethysmDual.plethysmDualEquivOf a b (dualEquiv V b) (dualEquiv (SymPow b V) a))
  · intro g
    exact PlethysmDual.plethysmDualEquivOf_adjoint b a
      (dualEquiv V a) (dualEquiv (SymPow a V) b) g
      (dualEquiv_natural V a g.toLinearMap)
      (dualEquiv_natural (SymPow a V) b (symPowMap a g.toLinearMap))
  · intro g
    exact PlethysmDual.plethysmDualEquivOf_adjoint a b
      (dualEquiv V b) (dualEquiv (SymPow b V) a) g
      (dualEquiv_natural V b g.toLinearMap)
      (dualEquiv_natural (SymPow b V) a (symPowMap b g.toLinearMap))
  · exact hsurj

end Problem346.PairingConstruction

end

end OAI
