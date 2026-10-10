import OAI.RepresentationTheory.FoulkesHowe.SymmetricPairing
import OAI.RepresentationTheory.FoulkesHowe.PairingPerfection

namespace OAI

noncomputable section
universe u
namespace Problem346

variable (n : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]

/-- The canonical symmetric-power pairing is perfect in finite dimension. -/
instance symPowDualMap_isPerfPair : (symPowDualMap n V).IsPerfPair :=
  symPowDual_isPerfPair_of_pure_evaluation V n (symPowDualMap n V)
    (symPowDualMap_pure_right n V) (symPowDualMap_pure_left n V)

/-- Symmetric powers commute with algebraic duality in finite dimension. -/
def symPowDualEquiv :
    SymPow n (Module.Dual ℂ V) ≃ₗ[ℂ] Module.Dual ℂ (SymPow n V) :=
  (symPowDualMap n V).toPerfPair

@[simp] theorem symPowDualEquiv_toLinearMap :
    (symPowDualEquiv n V).toLinearMap = symPowDualMap n V := rfl

@[simp] theorem symPowDualEquiv_apply (p : SymPow n (Module.Dual ℂ V))
    (q : SymPow n V) : symPowDualEquiv n V p q = symPowDualMap n V p q := rfl

@[simp] theorem symPowDualEquiv_monomial (φ : Fin n → Module.Dual ℂ V)
    (x : Fin n → V) :
    symPowDualEquiv n V (symMonomial n (Module.Dual ℂ V) φ) (symMonomial n V x) =
      permanentPairing n (fun φ x => φ x) φ x :=
  symPowDualMap_monomial n V φ x

end Problem346

end

end OAI
