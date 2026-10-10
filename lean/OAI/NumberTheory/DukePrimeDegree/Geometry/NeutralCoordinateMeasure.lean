import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralUpperRootHomeomorph
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLiftInvariance
import Mathlib.MeasureTheory.Measure.Comap

namespace OAI

/-! # Translation invariance in the actual neutral product chart -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem comap_map_eq_of_equivariant
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Z) (f : Y → Z) (hf : MeasurableEmbedding f)
    (e : Y ≃ᵐ Y) (g : Z ≃ᵐ Z)
    (heq : ∀ y, f (e y)=g (f y)) (hinv : ν.map g=ν) :
    (ν.comap f).map e=ν.comap f := by
  ext E hE
  have himage : f '' (e ⁻¹' E)=g ⁻¹' (f '' E) := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨e y,hy,heq y⟩
    · rintro ⟨y,hy,hyz⟩
      refine ⟨e.symm y,?_,?_⟩
      · change e (e.symm y) ∈ E
        simpa only [e.apply_symm_apply] using hy
      · apply g.injective
        rw [←heq,e.apply_symm_apply,hyz]
  rw [Measure.map_apply e.measurable hE,
    Measure.comap_apply f hf.injective (fun _ => hf.measurableSet_image.mpr) _
      (hE.preimage e.measurable),himage,
    ←Measure.map_apply g.measurable (hf.measurableSet_image.mpr hE),hinv,
    Measure.comap_apply f hf.injective (fun _ => hf.measurableSet_image.mpr) _ hE]

abbrev NeutralCoordinateBase (n : ℕ) := UnitDiagonalTransverse n × UpperRootTime n

def neutralProductParam (n : ℕ)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) : G n :=
  neutralUpperRootParam n (z.1.1,(z.1.2,z.2))

lemma neutralProductParam_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (neutralProductParam n) :=
  (neutralUpperRootParam_isOpenEmbedding n).comp
    (Homeomorph.prodAssoc _ _ _).isOpenEmbedding

lemma neutralProductParam_add (n : ℕ)
    (z : NeutralCoordinateBase n × transverseNeutralSpace n) (v : transverseNeutralSpace n) :
    neutralProductParam n (z.1,z.2+v)=
      neutralProductParam n z*diagonalOneParameter v.val v.prop 1 :=
  neutralUpperRootParam_translate n (z.1.1,(z.1.2,z.2)) v

def neutralCoordinateMeasure (n : ℕ) (ν : Measure (G n)) :
    Measure (NeutralCoordinateBase n × transverseNeutralSpace n) :=
  ν.comap (neutralProductParam n)

lemma neutralCoordinateBase_locallyCompact (n : ℕ) :
    LocallyCompactSpace (NeutralCoordinateBase n) := by
  let : LocallyCompactSpace (NeutralCoordinateBase n × transverseNeutralSpace n) :=
    (neutralProductParam_isOpenEmbedding n).locallyCompactSpace
  exact (isOpenQuotientMap_fst (X := NeutralCoordinateBase n)
    (Y := transverseNeutralSpace n)).locallyCompactSpace

lemma neutralCoordinateBase_secondCountable (n : ℕ) :
    SecondCountableTopology (NeutralCoordinateBase n) := by
  let : SecondCountableTopology (NeutralCoordinateBase n × transverseNeutralSpace n) :=
    (neutralProductParam_isOpenEmbedding n).isEmbedding.secondCountableTopology
  exact Topology.IsOpenQuotientMap.secondCountableTopology
    (isOpenQuotientMap_fst (X := NeutralCoordinateBase n) (Y := transverseNeutralSpace n))

theorem neutralCoordinateMeasure_finiteOnCompacts (n : ℕ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x) :
    IsFiniteMeasureOnCompacts (neutralCoordinateMeasure n (quotientLiftMeasure n μ s)) := by
  let := quotientLiftMeasure_locallyFinite n μ s hsm hs
  exact IsFiniteMeasureOnCompacts.comap' _
    (neutralProductParam_isOpenEmbedding n).continuous
    (neutralProductParam_isOpenEmbedding n).measurableEmbedding

theorem neutralCoordinateMeasure_translation (n : ℕ)
    (μ : Measure (X n)) (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (v : transverseNeutralSpace n)
    (hv : μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ) :
    (neutralCoordinateMeasure n (quotientLiftMeasure n μ s)).map
      (fun z => (z.1,z.2+v))=neutralCoordinateMeasure n (quotientLiftMeasure n μ s) := by
  let e := ((Homeomorph.refl (NeutralCoordinateBase n)).prodCongr
    (Homeomorph.addRight v)).toMeasurableEquiv
  let g := (Homeomorph.mulRight (diagonalOneParameter v.val v.prop 1)).toMeasurableEquiv
  exact comap_map_eq_of_equivariant (quotientLiftMeasure n μ s) (neutralProductParam n)
    (neutralProductParam_isOpenEmbedding n).measurableEmbedding e g
    (fun z => neutralProductParam_add n z v)
    (quotientLiftMeasure_right_invariant n μ s hsm hs _ hv)

end DukePrimeDegree

end

end OAI
