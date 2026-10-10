import OAI.Computability.DegreeRigidity.SetModels.ModelOmegaJump
import OAI.Computability.DegreeRigidity.Constructibility.PersistenceRealClosure

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open PersistentCountability
open TransitiveNameModel OracleJump PersistenceRealClosure PersistentRestrictions
open PersistentPresentation NumericalAutomorphism NumericalIdeal NumericalExtension
universe u

theorem sourceT_real_closed (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    PersistenceRealClosure.Closed (modelReals M) where
  lower := sourceT_real_lower M hM hT
  join := sourceT_real_join M hM hT
  omega := sourceT_real_omega_jump M hM hT

theorem sourceT_persistent_graph_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ modelReals M)
    (ρ : I ≃o I) (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier) :
    graphOracle hA ρ ∈ modelReals M :=
  graph_mem (sourceT_real_closed M hM hT) hA hAM ρ hp hz

theorem sourceT_persistent_extension_reals (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A) (hAM : A ∈ modelReals M)
    (ρ : I ≃o I) (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ Graph ρ hA v) {X : Oracle} (hX : X ∈ modelReals M) :
    ∃ H ∈ modelReals M, ∃ S ∈ modelReals M, JumpCode H ∧ Includes A H ∧
      (∃ n, degree X = degree (EncodedForcing.columns H n)) ∧
      Action H (fun v => S v = true) ∧
      Compatible A H (fun v => R v = true) (fun v => S v = true) :=
  extension_witnesses (sourceT_real_closed M hM hT) hA hAM ρ hp hz hR hX

end TuringRigidity.BoundedSetTheory

end OAI
