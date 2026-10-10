import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralHaarProduct

namespace OAI

/-! # Neutral Haar products in every left-translated chart -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem translated_neutral_product (n : ℕ) (g : G n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace n,
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace n)) [η.IsAddHaarMeasure]
    (K : Set (transverseNeutralSpace n)) (hK : IsCompact K) (hηK : η K=1) :
    (quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)=
      (firstCoordinateSlice
        ((quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)) K).prod η := by
  let F := fun z : NeutralCoordinateBase n × transverseNeutralSpace n =>
    g*neutralProductParam n z
  have hF : Topology.IsOpenEmbedding F :=
    (Homeomorph.mulLeft g).isOpenEmbedding.comp (neutralProductParam_isOpenEmbedding n)
  let := quotientLiftMeasure_locallyFinite n μ s hsm hs
  let := neutralCoordinateBase_locallyCompact n
  let := neutralCoordinateBase_secondCountable n
  let : IsFiniteMeasureOnCompacts ((quotientLiftMeasure n μ s).comap F) :=
    IsFiniteMeasureOnCompacts.comap' _ hF.continuous hF.measurableEmbedding
  apply translationInvariant_eq_product _ _ η K hK hηK
  intro v
  let e := ((Homeomorph.refl (NeutralCoordinateBase n)).prodCongr
    (Homeomorph.addRight v)).toMeasurableEquiv
  let a := (Homeomorph.mulRight (diagonalOneParameter v.val v.prop 1)).toMeasurableEquiv
  have H := comap_map_eq_of_equivariant (quotientLiftMeasure n μ s) F
    hF.measurableEmbedding e a (fun z => by
      change g*neutralProductParam n (z.1,z.2+v)=
        (g*neutralProductParam n z)*diagonalOneParameter v.val v.prop 1
      rw [neutralProductParam_add,mul_assoc])
    (quotientLiftMeasure_right_invariant n μ s hsm hs _ (hA v))
  have he : ⇑e = (fun z => (z.1,v+z.2)) := by
    funext z
    rcases z with ⟨z,w⟩
    change (z,w+v)=(z,v+w)
    rw [add_comm]
  rw [he] at H
  exact H

theorem translated_neutral_transverse_finiteOnCompacts (n : ℕ) (g : G n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (K : Set (transverseNeutralSpace n)) (hK : IsCompact K) :
    IsFiniteMeasureOnCompacts (firstCoordinateSlice
      ((quotientLiftMeasure n μ s).comap (fun z => g*neutralProductParam n z)) K) := by
  let := quotientLiftMeasure_locallyFinite n μ s hsm hs
  have hF : Topology.IsOpenEmbedding
      (fun z : NeutralCoordinateBase n × transverseNeutralSpace n =>
        g*neutralProductParam n z) :=
    (Homeomorph.mulLeft g).isOpenEmbedding.comp (neutralProductParam_isOpenEmbedding n)
  let : IsFiniteMeasureOnCompacts ((quotientLiftMeasure n μ s).comap
      (fun z => g*neutralProductParam n z)) :=
    IsFiniteMeasureOnCompacts.comap' _ hF.continuous hF.measurableEmbedding
  exact firstCoordinateSlice_finiteOnCompacts _ hK

end DukePrimeDegree

end

end OAI
