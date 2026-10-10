import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralCoordinateMeasure
import OAI.NumberTheory.DukePrimeDegree.Dynamics.TranslationInvariantProduct

namespace OAI

/-! # Haar product structure in the actual neutral coordinates -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutralCoordinateMeasure_product (n : ℕ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (hA : ∀ v : transverseNeutralSpace n,
      μ.map (fun x => rightAction x (diagonalOneParameter v.val v.prop 1))=μ)
    (η : Measure (transverseNeutralSpace n)) [η.IsAddHaarMeasure]
    (K : Set (transverseNeutralSpace n)) (hK : IsCompact K) (hηK : η K=1) :
    neutralCoordinateMeasure n (quotientLiftMeasure n μ s)=
      (firstCoordinateSlice (neutralCoordinateMeasure n (quotientLiftMeasure n μ s)) K).prod η := by
  let := neutralCoordinateBase_locallyCompact n
  let := neutralCoordinateBase_secondCountable n
  let := neutralCoordinateMeasure_finiteOnCompacts n μ s hsm hs
  apply translationInvariant_eq_product _ _ η K hK hηK
  intro v
  simpa only [add_comm] using neutralCoordinateMeasure_translation n μ s hsm hs v (hA v)

end DukePrimeDegree

end

end OAI
