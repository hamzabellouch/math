import OAI.Computability.DegreeRigidity.CohenForcing.CohenColumnRealValue
import OAI.Computability.DegreeRigidity.SetModels.ProjectedArithmeticOutputCone

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenProjectedGeneric InternalCohenFactor
open OracleJump TableIndices IndexMatrix PersistentRestrictions SetDegreeDecoding
open ElementaryModel FullSetForcing CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem selected_column_arithmetic_cone (M K a : ZFSet.{0}) [Countable (Conditions M)]
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
    (p₀ : Conditions (poset K)) (hp₀ : p₀ ∈ G.carrier) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ d : ℕ, ∃ p ∈ G.carrier, p ≤ p₀ ∧
      ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
        project C B hBC p ∈ (projected C B hBC H).carrier →
        ∃ A X : Oracle, (realName K a).val H.carrier = realCode A ∧
          (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (InternalCohen.bitSet b) ∈
            InternalCollapse.unionGraph H ↔ A n = b) ∧
          Represents (iterate (join A R) 5) (machine d) X ∧
          ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
            realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier := by
  intro C B hBC
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  obtain ⟨A,hτv,_,_,_⟩ := projected_real_value M K a hM hT hK ha G hG
  obtain ⟨x,y,_,_,_,hxv,d,p,hp,hp₀',hcone⟩ :=
    projected_arithmetic_output_cone M C B hM hT hC hB hBC δ Z φ I ρ hz R hRM hR
      f hf hfv G hG hOwn (realName {a} a)
      (realName_internal M {a} a hM hT hsingle (ZFSet.mem_singleton.mpr rfl))
      A hτv p₀ hp₀
  refine ⟨d,p,hp,hp₀',fun H hH hpH => ?_⟩
  obtain ⟨A',X,hx,_,hrep,hout⟩ := hcone H hH hpH
  obtain ⟨AH,hτH,hfull,hbits,_⟩ := projected_real_value M K a hM hT hK ha H hH
  have he : A' = AH := realCode_injective
    (hx.symm.trans ((hxv H hH (hτH.symm ▸ realCode_subset AH)).trans hτH))
  subst A'
  exact ⟨AH,X,hfull,hbits,hrep,hout⟩

end TuringRigidity.BoundedForcing

end OAI
