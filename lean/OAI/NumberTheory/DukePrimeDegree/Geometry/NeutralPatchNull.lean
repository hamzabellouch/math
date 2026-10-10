import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralAtomicPatch
import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralGraphLifts

namespace OAI

/-! # Transfer the neutral graph's full measure to the quotient patch -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev neutralQuotientParam (n : ℕ) (g : G n)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) : X n :=
  Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (g*neutralProductParam n z)

lemma neutralQuotientParam_continuous (n : ℕ) (g : G n) :
    Continuous (neutralQuotientParam n g) :=
  continuous_quotient_mk'.comp (continuous_const.mul
    (neutralProductParam_isOpenEmbedding n).continuous)

lemma neutralQuotientParam_injOn (n : ℕ) (g : G n)
    (B : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
      (emptyRootPattern n) (completeRootChain_final n) g)
    (R : Set (NeutralCoordinateBase n × transverseNeutralSpace n))
    (hRB : ∀ z ∈ R, neutralToPrefix n z ∈ B.domain) :
    InjOn (neutralQuotientParam n g) R := by
  intro z hz w hw hzw
  have he : B.param ⟨neutralToPrefix n z,hRB z hz⟩ =
      B.param ⟨neutralToPrefix n w,hRB w hw⟩ := by
    change Quotient.mk _ ((neutralEmptyPrefix n).timeGroupParam
      (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) g
      (neutralToPrefix n z)) = Quotient.mk _ ((neutralEmptyPrefix n).timeGroupParam
      (completeRootChain n) (emptyRootPattern n) (completeRootChain_final n) g
      (neutralToPrefix n w))
    simpa only [neutralToPrefix_param,neutralQuotientParam] using hzw
  exact (neutralToPrefix_isOpenEmbedding n).injective
    (congrArg Subtype.val (B.embedding.injective he))

theorem neutralQuotientParam_image_measure (n : ℕ) (g : G n)
    (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (E : Set (NeutralCoordinateBase n × transverseNeutralSpace n)) (hE : MeasurableSet E)
    (hinj : InjOn (neutralQuotientParam n g) E) :
    μ (neutralQuotientParam n g '' E)=
      (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z) E := by
  let f := fun z => g*neutralProductParam n z
  have hf : MeasurableEmbedding f :=
    ((Homeomorph.mulLeft g).isOpenEmbedding.comp
      (neutralProductParam_isOpenEmbedding n)).measurableEmbedding
  rw [hf.comap_apply,quotientLiftMeasure_injective_chart n μ s hsm hs (f '' E)
    (hf.measurableSet_image.mpr hE)]
  · rw [Set.image_image]
  · rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩ hzw
    exact congrArg f (hinj hz hw hzw)

theorem neutralQuotientParam_measurable_image (n : ℕ) (g : G n)
    (E : Set (NeutralCoordinateBase n × transverseNeutralSpace n)) (hE : MeasurableSet E)
    (hinj : InjOn (neutralQuotientParam n g) E) :
    MeasurableSet (neutralQuotientParam n g '' E) := by
  let f := fun z => g*neutralProductParam n z
  have hf : MeasurableEmbedding f :=
    ((Homeomorph.mulLeft g).isOpenEmbedding.comp
      (neutralProductParam_isOpenEmbedding n)).measurableEmbedding
  have hq : InjOn (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) (f '' E) := by
    rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩ hzw
    exact congrArg f (hinj hz hw hzw)
  have H := (hf.measurableSet_image.mpr hE).image_of_measurable_injOn
    continuous_quotient_mk'.measurable hq
  rw [Set.image_image] at H
  change MeasurableSet (neutralQuotientParam n g '' E) at H
  exact H

theorem neutral_patch_image_ae_graph (n : ℕ) (g : G n)
    (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (τ : Measure (NeutralCoordinateBase n)) [SFinite τ]
    (η : Measure (transverseNeutralSpace n)) [SFinite η]
    (hprod : (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)=τ.prod η)
    (A : Set (NeutralCoordinateBase n)) (hA : MeasurableSet A)
    (K : Set (transverseNeutralSpace n)) (hK : MeasurableSet K)
    (hinj : InjOn (neutralQuotientParam n g) (A ×ˢ K))
    (F : Set (NeutralCoordinateBase n)) (hF : MeasurableSet F)
    (hfull : ∀ᵐ z ∂(τ.restrict A).prod (η.restrict K), z.1 ∈ F) :
    ∀ᵐ x ∂μ, x ∈ neutralQuotientParam n g '' (A ×ˢ K) →
      x ∈ neutralQuotientParam n g '' ((A ×ˢ K) ∩ Prod.fst ⁻¹' F) := by
  let E := (A ×ˢ K) ∩ Prod.fst ⁻¹' Fᶜ
  have hE : MeasurableSet E := (hA.prod hK).inter (hF.compl.preimage measurable_fst)
  have he0 : μ (neutralQuotientParam n g '' E)=0 := by
    rw [neutralQuotientParam_image_measure n g μ s hsm hs E hE
      (hinj.mono inter_subset_left),hprod]
    have he := ae_iff.mp hfull
    rw [Measure.prod_restrict] at he
    change ((τ.prod η).restrict (A ×ˢ K)) (Prod.fst ⁻¹' Fᶜ)=0 at he
    rw [Measure.restrict_apply (hF.compl.preimage measurable_fst)] at he
    change (τ.prod η) ((A ×ˢ K) ∩ Prod.fst ⁻¹' Fᶜ)=0
    rw [Set.inter_comm]
    exact he
  have hn : ∀ᵐ x ∂μ, x ∉ neutralQuotientParam n g '' E := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using he0
  filter_upwards [hn] with x hx hmem
  obtain ⟨z,hz,rfl⟩ := hmem
  by_cases hf : z.1 ∈ F
  · exact ⟨z,⟨hz,hf⟩,rfl⟩
  · exact (hx ⟨z,⟨hz,hf⟩,rfl⟩).elim

end DukePrimeDegree

end

end OAI
