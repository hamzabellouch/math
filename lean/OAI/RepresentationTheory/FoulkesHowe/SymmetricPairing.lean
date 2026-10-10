import OAI.RepresentationTheory.FoulkesHowe.PermanentPairing
import OAI.RepresentationTheory.FoulkesHowe.PairingLift

namespace OAI

noncomputable section
universe u v
namespace Problem346

variable {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- The normalized symmetric-power pairing induced by a bilinear pairing. -/
def symPowPairing (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    SymPow n X →ₗ[ℂ] Module.Dual ℂ (SymPow n Y) :=
  Classical.choose (exists_symPow_bilinear_lift n n X Y
    (permanentPairingMultilinear n B)
    (fun σ x => permanentPairingMultilinear_perm_left n B x σ)
    (fun x σ y => permanentPairingMultilinear_perm_right n B x y σ))

@[simp] theorem symPowPairing_monomial (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (x : Fin n → X) (y : Fin n → Y) :
    symPowPairing n B (symMonomial n X x) (symMonomial n Y y) =
      permanentPairing n (fun x y => B x y) x y := by
  simpa only [symPowPairing, permanentPairingMultilinear_apply] using
    Classical.choose_spec (exists_symPow_bilinear_lift n n X Y
    (permanentPairingMultilinear n B)
    (fun σ x => permanentPairingMultilinear_perm_left n B x σ)
    (fun x σ y => permanentPairingMultilinear_perm_right n B x y σ)) x y

/-- The canonical pairing from the symmetric power of the dual space. -/
def symPowDualMap (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] :
    SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V) :=
  symPowPairing n (LinearMap.id : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V)

@[simp] theorem symPowDualMap_monomial (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : Fin n → Module.Dual ℂ V) (x : Fin n → V) :
    symPowDualMap n V (symMonomial n (Module.Dual ℂ V) φ) (symMonomial n V x) =
      permanentPairing n (fun φ x => φ x) φ x :=
  symPowPairing_monomial n (LinearMap.id : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V) φ x

/-- On pure powers, the pairing is ordinary algebra evaluation. -/
theorem symPowDualMap_pure_right (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (p : SymPow n (Module.Dual ℂ V)) (x : V) :
    symPowDualMap n V p (symMonomial n V (fun _ => x)) =
      SymmetricAlgebra.lift (Module.Dual.eval ℂ V x) p.val := by
  have h : (symPowDualMap n V).flip (symMonomial n V (fun _ => x)) =
      (SymmetricAlgebra.lift (Module.Dual.eval ℂ V x)).toLinearMap.domRestrict
        (symPowSubmodule n (Module.Dual ℂ V)) := by
    apply SymmetricLift.linearMap_ext
    intro φ
    change symPowDualMap n V (symMonomial n (Module.Dual ℂ V) φ)
      (symMonomial n V (fun _ => x)) = _
    rw [symPowDualMap_monomial]
    simp [symMonomial, symMonomialRaw]
  exact congrArg (fun L : SymPow n (Module.Dual ℂ V) →ₗ[ℂ] ℂ => L p) h

/-- The analogous pure-power evaluation in the dual variables. -/
theorem symPowDualMap_pure_left (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (φ : Module.Dual ℂ V) (p : SymPow n V) :
    symPowDualMap n V (symMonomial n (Module.Dual ℂ V) (fun _ => φ)) p =
      SymmetricAlgebra.lift φ p.val := by
  have h : symPowDualMap n V (symMonomial n (Module.Dual ℂ V) (fun _ => φ)) =
      (SymmetricAlgebra.lift φ).toLinearMap.domRestrict (symPowSubmodule n V) := by
    apply SymmetricLift.linearMap_ext
    intro x
    rw [symPowDualMap_monomial]
    simp [symMonomial, symMonomialRaw]
  exact congrArg (fun L : SymPow n V →ₗ[ℂ] ℂ => L p) h

end Problem346

end

end OAI
