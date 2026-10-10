import OAI.Computability.DegreeRigidity.Representation.NativeGenericWitness
import OAI.Computability.DegreeRigidity.Constructibility.RelativePersistentDescent
import OAI.Computability.DegreeRigidity.Constructibility.FixedRelativeGround
import OAI.Computability.DegreeRigidity.Representation.CommonGenericModels

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ArithmeticTree CountableForcing
universe u

theorem generically_persistent_ground_graph_descent (M N : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hTM : SourceT M)
    (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (ρ : modelIdeal M hM hTM ≃o modelIdeal M hM hTM)
    (hρN : automorphismSet ρ ∈ N)
    (hgen : SetGenericallyPersistent N (modelIdeal M hM hTM) ρ) :
    automorphismSet ρ ∈ relativeModel M (groundReals M) := by
  have hI := relativeModel_subset M _ (ground_idealSet_mem_relativeModel M hM hTM)
  have hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ (modelIdeal M hM hTM).carrier :=
    ⟨_,sourceT_real_jump M hM hTM (sourceT_zero_real M hM hTM),rfl⟩
  exact persistent_modelIdeal_graph_mem_relativeModel M hM hTM ρ
    (hgen.persistent hN hTN (hMN hI) hρN hz)

theorem generic_extension_graph_descent (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {c o : ZFSet.{u}}
    [Preorder (Conditions c)] [OrderTop (Conditions c)]
    (hc : c ∈ M) (ho : o ∈ M)
    (hos : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρG : automorphismSet ρ ∈ genericExtensionSet M c G.carrier)
    (hgen : SetGenericallyPersistent (genericExtensionSet M c G.carrier) (modelIdeal M hM hT) ρ) :
    automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
      automorphismSet ρ ∈ M ∧
      relativeModel (genericExtensionSet M c G.carrier) (groundReals M) =
        relativeModel M (groundReals M) := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht := G.upper le_top hp
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  have hd := generically_persistent_ground_graph_descent M _ hM hT
    (genericExtensionSet_transitive M c hM G.carrier)
    (extension_sourceT M hM hT hc ho hos G hG ht) hME ρ hρG hgen
  exact ⟨hd,relativeModel_subset M _ hd,
    relativeModel_generic_fixed_parameter M hM hT (groundReals_mem M hM hT) hc ho hos G hG⟩

theorem generic_persistence_returns_to_ground (M N : ZFSet.{u})
    [Countable (Conditions M)] (hM : Transitive M) (hTM : SourceT M)
    (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (ρ : modelIdeal M hM hTM ≃o modelIdeal M hM hTM)
    (hρN : automorphismSet ρ ∈ N)
    (hgen : SetGenericallyPersistent N (modelIdeal M hM hTM) ρ) :
    SetGenericallyPersistent M (modelIdeal M hM hTM) ρ := by
  have hI := relativeModel_subset M _ (ground_idealSet_mem_relativeModel M hM hTM)
  have hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ (modelIdeal M hM hTM).carrier :=
    ⟨_,sourceT_real_jump M hM hTM (sourceT_zero_real M hM hTM),rfl⟩
  have hρM := relativeModel_subset M _
    (generically_persistent_ground_graph_descent M N hM hTM hN hTN hMN ρ hρN hgen)
  exact (setGenericallyPersistent_iff M hM hTM _ hI ρ hρM hz).mpr
    (hgen.persistent hN hTN (hMN hI) hρN hz)

end TuringRigidity.RelativeConstructible

end OAI
