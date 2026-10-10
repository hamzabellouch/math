import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationJet

namespace OAI

/-! The variance generator requires only two derivatives of its bounded
test. In particular it applies to the ordinary curvature without
requiring a fifth derivative of the finite scalar field. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

structure MagneticContinuationTwoJet where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ
  mValue : Measurable value
  mFirst : Measurable first
  mSecond : Measurable second
  bValue : MagneticContinuationBound value
  bFirst : MagneticContinuationBound first
  bSecond : MagneticContinuationBound second
  dValue : ∀ z, HasDerivAt value (first z) z
  dFirst : ∀ z, HasDerivAt first (second z) z

def MagneticContinuationJet.toTwoJet (P : MagneticContinuationJet) :
    MagneticContinuationTwoJet where
  value := P.value
  first := P.first
  second := P.second
  mValue := P.mValue
  mFirst := P.mFirst
  mSecond := P.mSecond
  bValue := P.bValue
  bFirst := P.bFirst
  bSecond := P.bSecond
  dValue := P.dValue
  dFirst := P.dFirst

def MagneticContinuationJet.slopeTwoJet (P : MagneticContinuationJet) :
    MagneticContinuationTwoJet where
  value := P.first
  first := P.second
  second := P.third
  mValue := P.mFirst
  mFirst := P.mSecond
  mSecond := P.mThird
  bValue := P.bFirst
  bFirst := P.bSecond
  bSecond := P.bThird
  dValue := P.dFirst
  dFirst := P.dSecond

end InvariantIsing

end

end OAI
