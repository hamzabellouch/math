import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetReesReduction
import OAI.NumberTheory.PiExponent.Ampleness.GlobalReesCanonicalRecovery

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact eventual_blowup_jetRestriction_surjective_of_affine_recovery p I A hample
    (fun U => GlobalReesRecoveryComparison.eventually_ordinaryMap_app_bijective I U)

end
end PiExponent.BlowupJetSurjectivity

end OAI
