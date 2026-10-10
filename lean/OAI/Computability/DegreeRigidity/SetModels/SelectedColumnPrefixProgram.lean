import OAI.Computability.DegreeRigidity.SetModels.SelectedColumnArithmeticCone
import OAI.Computability.DegreeRigidity.CohenForcing.CohenColumnPrefixCone

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenProjectedGeneric InternalCohenFactor
open OracleJump TableIndices IndexMatrix PersistentRestrictions SetDegreeDecoding
open ElementaryModel FullSetForcing CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem selected_column_prefix_program (M K a : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm)
    (I : CountableIdeal) (ρ : I ≃o I)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hRM : realCode R ∈ M)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (f : Name (Conditions (poset K))) (hf : f.encode (label (poset K)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (hOwn : OwnDegreeExtension (genericExtensionSet M (poset K) G.carrier)
      (idealSet I) (automorphismSet ρ) (f.val G.carrier))
    : ∃ A₀ : Oracle, ∃ d N : ℕ,
      (realName K a).val G.carrier = realCode A₀ ∧
      ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
        ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
          (∀ n < N, A n = A₀ n) → ∃ X : Oracle,
          Represents (iterate (join A R) 5) (machine d) X ∧
          ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
            realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier := by
  obtain ⟨d,p,hp,_,hcone⟩ := selected_column_arithmetic_cone M K a hM hT hK ha
    δ Z φ I ρ hz R hRM hR f hf hfv G hG hOwn ⊤ (G.upper le_top G.nonempty.choose_spec)
  obtain ⟨A₀,hA₀,N,hprefix⟩ := selected_prefix_cone M K a hM hT hK ha G hG p hp
  refine ⟨A₀,d,N,hA₀,fun H hH A hA hearly => ?_⟩
  obtain ⟨AH,X,hAH,_,hrep,hout⟩ := hcone H hH (hprefix H hH A hA hearly)
  have he : AH = A := realCode_injective (hAH.symm.trans hA)
  subst AH
  exact ⟨X,hrep,hout⟩

end TuringRigidity.BoundedForcing

end OAI
