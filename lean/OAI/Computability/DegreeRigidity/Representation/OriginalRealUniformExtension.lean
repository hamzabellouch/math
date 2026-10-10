import OAI.Computability.DegreeRigidity.Representation.OriginalRealUniformDefinition
import OAI.Computability.DegreeRigidity.Effective.UniformCohenDefinitionExtension

namespace OAI

namespace TuringRigidity.OriginalRealDefinitionTransport
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem original_uniform_extension (M K I ρ : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hK : FirstUncountable M K) (hI : I ∈ M) (hρ : ρ ∈ M)
    (τ f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (hf : f.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : GroundGeneric M G) (hreal : τ.val G.carrier ⊆ ZFSet.omega)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (φ : SentenceForm)
    (hX : τ.val G.carrier ∈ level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
    (hdef : f.val G.carrier = definedSubset (level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
        φ (fun _ : Fin φ.bound => τ.val G.carrier))
    (hext : OwnDegreeExtension
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier) I ρ (f.val G.carrier)) :
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let X := τ.val G.carrier
    let N := RealGeneratedModel.hull M X
    RealGeneratedModel.Contains M X N ∧ (N : Set ZFSet.{0}).Countable ∧
      ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
        (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
          fX.val H.carrier = definedSubset
            (level (groundReals (genericExtensionSet N c H.carrier)) δ)
              φ (fun _ : Fin φ.bound => X) ∧
          OwnDegreeExtension (genericExtensionSet N c H.carrier) I ρ (fX.val H.carrier)) ∧
        ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
          genericExtensionSet N c GX.carrier = genericExtensionSet M c G.carrier ∧
          fX.val GX.carrier = f.val G.carrier := by
  intro c X N
  obtain ⟨hN,f₀,_,hf₀,GX,hGX,hExt,hval₀,_⟩ :=
    original_uniform_definition M K hM hT hK τ f hτ hf G hG hreal δ hδ φ hX hdef
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK.2.1 (sourceT_omega_mem M hM hT)
  have hc : c ∈ N := hN.2.2.1 (conditions_mem M _ hM hT hA)
  have hNE : N ⊆ genericExtensionSet M c G.carrier := by
    rw [←hExt]
    obtain ⟨q,hq⟩ := GX.nonempty
    exact ground_inclusion_set N c hN.1 hN.2.1.pairing hN.2.1.union hN.2.1.powerSet
      hN.2.1.separation.finitePrefix.bounded hN.2.1.replacement.finitePrefix hN.2.1.infinity
      hc GX.carrier (GX.upper le_top hq)
  have hNct : (N : Set ZFSet.{0}).Countable := by
    have hEct : (genericExtensionSet M c G.carrier : Set ZFSet.{0}).Countable := by
      rw [genericExtensionSet_coe]
      exact genericExtension_countable M c hct G.carrier
    exact hEct.mono hNE
  have h₀ : OwnDegreeExtension (genericExtensionSet N c GX.carrier) I ρ
      (definedSubset (level (groundReals (genericExtensionSet N c GX.carrier)) δ)
        φ (fun _ : Fin φ.bound => X)) := by
    rw [←hf₀ GX hGX,hval₀,hExt]
    exact hext
  obtain ⟨fX,hfX,hfv⟩ := uniform_cohen_definition_extension N (ZFSet.prod K ZFSet.omega) I ρ
    hN.1 hN.2.1 hNct (hN.2.2.1 hA) (hN.2.2.1 hI) (hN.2.2.1 hρ)
    δ (hN.2.2.1 hδ) X hN.2.2.2 φ GX hGX h₀
  exact ⟨hN,hNct,fX,hfX,hfv,GX,hGX,hExt,
    (hfv GX hGX).1.trans ((hf₀ GX hGX).symm.trans hval₀)⟩

end TuringRigidity.OriginalRealDefinitionTransport

end OAI
