import OAI.RepresentationTheory.FoulkesHowe.SymmetricDual
import OAI.RepresentationTheory.FoulkesHowe.FiniteDimension

namespace OAI

noncomputable section
universe u
namespace Problem346

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- Evaluation on pure dual powers detects the second variable of a pairing. -/
theorem symPowDual_flip_injective_of_pure_evaluation (n : ℕ)
    (B : SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V))
    (hB : ∀ (φ : Module.Dual ℂ V) (p : SymPow n V),
      B (symMonomial n (Module.Dual ℂ V) (fun _ => φ)) p =
        SymmetricAlgebra.lift φ p.val) :
    Function.Injective B.flip := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply symAlg_eq_zero_of_lift_eq_zero V
  intro φ
  rw [map_sub, ← hB φ p, ← hB φ q]
  have h := congrArg
    (fun f : Module.Dual ℂ (SymPow n (Module.Dual ℂ V)) =>
      f (symMonomial n (Module.Dual ℂ V) (fun _ => φ))) hpq
  exact sub_eq_zero.mpr h

/-- Pure-power evaluation identities characterize a perfect symmetric-power pairing. -/
theorem symPowDual_isPerfPair_of_pure_evaluation [FiniteDimensional ℂ V] (n : ℕ)
    (B : SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V))
    (hRight : ∀ (p : SymPow n (Module.Dual ℂ V)) (x : V),
      B p (symMonomial n V (fun _ => x)) =
        SymmetricAlgebra.lift (Module.Dual.eval ℂ V x) p.val)
    (hLeft : ∀ (φ : Module.Dual ℂ V) (p : SymPow n V),
      B (symMonomial n (Module.Dual ℂ V) (fun _ => φ)) p =
        SymmetricAlgebra.lift φ p.val) : B.IsPerfPair :=
  LinearMap.IsPerfPair.of_injective'
    (symPowDual_injective_of_pure_evaluation V n B hRight)
    (symPowDual_flip_injective_of_pure_evaluation V n B hLeft)

end Problem346

end

end OAI
