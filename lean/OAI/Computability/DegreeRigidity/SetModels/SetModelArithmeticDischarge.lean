import OAI.Computability.DegreeRigidity.SetModels.SetModelInternalRelations
import OAI.Computability.DegreeRigidity.SetModels.SetModelArithmeticInterface

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open SetDegreeDecoding PersistentRestrictions PersistentPresentation
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem realClosure (C : Context M) : PersistenceRealClosure.Closed (reals M) := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  exact realClosure_of_lower_and_jump M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc

theorem persistent_sets (C : Context M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    idealSet I ∈ M ∧ automorphismSet ρ ∈ M := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  exact persistent_model_sets M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc hE hEc hA hAM ρ hρ hz

theorem persistent_extension_sets (C : Context M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M := by
  obtain ⟨g,hg,hgc⟩ := internal_jump_graph C
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  exact persistent_model_extension_sets M C.transitive C.pairing C.union C.power C.separation C.infinity
    (lower_mem C) (fun _ h => jump_mem C h) hg hgc hE hEc hA hAM ρ hρ hz hX

end
end TuringRigidity.SetModelSyntax

end OAI
