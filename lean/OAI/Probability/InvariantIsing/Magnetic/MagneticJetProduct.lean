import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationJet

namespace OAI

/-! The finite third-order product needed for the fourth derivative of the
actual scalar Gaussian transition. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing
lemma MagneticContinuationJet.eq_of_value_eq (A B : MagneticContinuationJet)
    (h : A.value = B.value) : A = B := by
  have h1 : A.first = B.first := by
    funext z
    exact (A.dValue z).unique (h ▸ B.dValue z)
  have h2 : A.second = B.second := by
    funext z
    exact (A.dFirst z).unique (h1 ▸ B.dFirst z)
  have h3 : A.third = B.third := by
    funext z
    exact (A.dSecond z).unique (h2 ▸ B.dSecond z)
  cases A
  cases B
  cases h
  cases h1
  cases h2
  cases h3
  rfl

namespace MagneticContinuationJet

def mul (A B : MagneticContinuationJet) : MagneticContinuationJet where
  value := fun z => A.value z * B.value z
  first := fun z => A.first z * B.value z + A.value z * B.first z
  second := fun z => A.second z * B.value z + 2 * A.first z * B.first z + A.value z * B.second z
  third := fun z => A.third z * B.value z + 3 * A.second z * B.first z +
    3 * A.first z * B.second z + A.value z * B.third z
  mValue := A.mValue.mul B.mValue
  mFirst := (A.mFirst.mul B.mValue).add (A.mValue.mul B.mFirst)
  mSecond := ((A.mSecond.mul B.mValue).add ((measurable_const.mul A.mFirst).mul B.mFirst)).add
    (A.mValue.mul B.mSecond)
  mThird := (((A.mThird.mul B.mValue).add ((measurable_const.mul A.mSecond).mul B.mFirst)).add
    ((measurable_const.mul A.mFirst).mul B.mSecond)).add (A.mValue.mul B.mThird)
  bValue := A.bValue.mul B.bValue
  bFirst := (A.bFirst.mul B.bValue).add (A.bValue.mul B.bFirst)
  bSecond := ((A.bSecond.mul B.bValue).add
    (((MagneticContinuationBound.const 2).mul A.bFirst).mul B.bFirst)).add (A.bValue.mul B.bSecond)
  bThird := (((A.bThird.mul B.bValue).add
    (((MagneticContinuationBound.const 3).mul A.bSecond).mul B.bFirst)).add
    (((MagneticContinuationBound.const 3).mul A.bFirst).mul B.bSecond)).add (A.bValue.mul B.bThird)
  dValue := fun z => (A.dValue z).mul (B.dValue z)
  dFirst := fun z => by
    convert ((A.dFirst z).mul (B.dValue z)).add ((A.dValue z).mul (B.dFirst z)) using 1
    ring
  dSecond := fun z => by
    convert (((A.dSecond z).mul (B.dValue z)).add
      (((A.dFirst z).const_mul 2).mul (B.dFirst z))).add
        ((A.dValue z).mul (B.dSecond z)) using 1
    ring

end MagneticContinuationJet
end InvariantIsing

end

end OAI
