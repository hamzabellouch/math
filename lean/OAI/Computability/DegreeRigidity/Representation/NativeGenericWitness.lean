import OAI.Computability.DegreeRigidity.Representation.NativeModelCompatibility
import OAI.Computability.DegreeRigidity.Representation.GroundGenericRequirements

namespace OAI

namespace TuringRigidity.ArithmeticTree
open BoundedSetTheory TransitiveNameModel SetDegreeDecoding PersistentRestrictions
open CountableForcing AtomicForcing
universe u

def SetGenericallyPersistent (M : ZFSet.{u}) (I : CountableIdeal) (ρ : I ≃o I) : Prop :=
  ∃ c o : ZFSet.{u}, ∃ ord : Preorder (Conditions c),
    letI := ord
    ∃ ot : OrderTop (Conditions c),
      letI := ot
      c ∈ M ∧ o ∈ M ∧
      (∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) ∧
      ∃ G : GenericFilter (Conditions c), GroundGeneric M G ∧
        SetModelCountability.InternallyCountable (genericExtensionSet M c G.carrier) (idealSet I) ∧
        NativePersistent (genericExtensionSet M c G.carrier) I ρ

theorem SetGenericallyPersistent.persistent {M : ZFSet.{u}}
    (hM : Transitive M) (hT : SourceT M) {I : CountableIdeal}
    (hI : idealSet I ∈ M) {ρ : I ≃o I} (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (h : SetGenericallyPersistent M I ρ) : Persistent I ρ := by
  obtain ⟨c,o,ord,ot,hc,ho,hos,G,hG,hct,hn⟩ := h
  let := ord
  let := ot
  obtain ⟨p,hp⟩ := G.nonempty
  exact (generic_nativePersistent_iff M hM hT hc ho hos G hG
    (G.upper le_top hp) I hI ρ hρ hz hct).mp hn

theorem setGenericallyPersistent_iff (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (I : CountableIdeal)
    (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    SetGenericallyPersistent M I ρ ↔ Persistent I ρ := by
  constructor
  · exact SetGenericallyPersistent.persistent hM hT hI hρ hz
  · intro hp
    obtain ⟨c,hc,hdef⟩ := InternalCollapse.conditions_exist M hM hT hI
    have h0 : (∅ : ZFSet.{u}) ∈ c := (hdef ∅).mpr
      ⟨hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero,InternalCollapse.prefix_empty _⟩
    let := InternalCollapse.order c
    let := InternalCollapse.collapsePreorder c
    let := InternalCollapse.top c h0
    have ho := InternalCollapse.orderSet_mem M hM hT hc
    obtain ⟨G,ht,hG⟩ := AtomicForcing.countable_ground_generic M ⟨c,hc⟩ (⊤ : Conditions c)
    have hne : ∃ x, x ∈ idealSet.{u} I := by
      obtain ⟨d,hd⟩ := I.nonempty
      exact ⟨degreeSet d,(mem_idealSet I _).mpr ⟨d,hd,rfl⟩⟩
    have hcount := InternalCollapse.internal_counting M hM hT hI hc hdef hne G hG
    have hE := genericExtensionSet_transitive M c hM G.carrier
    have hTE := extension_sourceT M hM hT hc ho (InternalCollapse.orderSet_pair c) G hG ht
    have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
    have hct := (native_countability_iff _ hE hTE (hME hI)).mpr hcount
    exact ⟨c,InternalCollapse.orderSet c,inferInstance,inferInstance,hc,ho,
      InternalCollapse.orderSet_pair c,G,hG,hct,
      (generic_nativePersistent_iff M hM hT hc ho (InternalCollapse.orderSet_pair c)
        G hG ht I hI ρ hρ hz hct).mpr hp⟩

end TuringRigidity.ArithmeticTree

end OAI
