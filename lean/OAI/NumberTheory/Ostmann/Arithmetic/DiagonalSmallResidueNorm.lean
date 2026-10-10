import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open Construction
open scoped BigOperators

theorem actual_small_average (d : Decomposition) (D P q : ℕ)
    (outerU xs : List SmallSlot) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    [NeZero (∏ i, smallPrime xs outerU i)]
    (h : SmallUnitData D P q outerU xs v) :
    (∑ z : ZMod (∏ i, smallPrime xs outerU i) × (ZMod (∏ i, smallPrime xs outerU i))ˣ,
      crtTest (smallPrime xs outerU) h.coprime (smallRetained xs outerU)
        (fun i => residueTransform d (smallPrime xs outerU i))
        (smallCoefficients D outerU xs v h.frequency h.denominator) z) /
      Fintype.card (ZMod (∏ i, smallPrime xs outerU i) × (ZMod (∏ i, smallPrime xs outerU i))ˣ) =
      ∏ i : Fin outerU.length, (((outerU[i].value-1:ℕ):ℝ)/outerU[i].value) := by
  rw [actual_crtTest_average,Fintype.prod_sum_type]
  simp only [smallPrime,smallRetained,localDensity,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,one_mul]

theorem actual_small_average_le_one (d : Decomposition) (D P q : ℕ)
    (outerU xs : List SmallSlot) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    [NeZero (∏ i, smallPrime xs outerU i)]
    (h : SmallUnitData D P q outerU xs v) :
    (∑ z : ZMod (∏ i, smallPrime xs outerU i) × (ZMod (∏ i, smallPrime xs outerU i))ˣ,
      crtTest (smallPrime xs outerU) h.coprime (smallRetained xs outerU)
        (fun i => residueTransform d (smallPrime xs outerU i))
        (smallCoefficients D outerU xs v h.frequency h.denominator) z) /
      Fintype.card (ZMod (∏ i, smallPrime xs outerU i) × (ZMod (∏ i, smallPrime xs outerU i))ˣ) ≤ 1 := by
  rw [actual_small_average d D P q outerU xs v h]
  apply Finset.prod_le_one₀
  · intro i hi
    positivity
  · intro i hi
    exact (localDensity_bounds _
      (Fact.out : (smallPrime xs outerU (.inr i)).Prime).pos false).2

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
