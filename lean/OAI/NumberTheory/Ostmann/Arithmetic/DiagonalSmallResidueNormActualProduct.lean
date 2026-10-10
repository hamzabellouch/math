import OAI.NumberTheory.Ostmann.Arithmetic.DiagonalSmallResidueNormActualBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.DiagonalSmallResidueNorm
open Construction Classical
open scoped BigOperators

abbrev SmallIndex (xs outerU : List SmallSlot) := Fin xs.length ⊕ Fin outerU.length

def smallPrime (xs outerU : List SmallSlot) : SmallIndex xs outerU → ℕ
  | .inl i => xs[i].value
  | .inr i => outerU[i].value

def smallRetained (xs outerU : List SmallSlot) : SmallIndex xs outerU → Bool
  | .inl _ => true
  | .inr _ => false

def smallCoefficients (D : ℕ) (outerU xs : List SmallSlot) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hv : ∀ i : Fin xs.length, IsUnit (v : ZMod xs[i].value))
    (hA : ∀ i : Fin xs.length,
      IsUnit (coefficientDenominator D outerU xs xs[i].value : ZMod xs[i].value)) :
    ∀ i, (ZMod (smallPrime xs outerU i))ˣ
  | .inl i => coefficientUnit v (coefficientDenominator D outerU xs xs[i].value) (hv i) (hA i)
  | .inr _ => 1

def smallResidues (P q : ℕ) (xs outerU : List SmallSlot)
    (hq : ∀ i, IsUnit (q : ZMod (smallPrime xs outerU i))) : LocalPair (smallPrime xs outerU) :=
  fun i => ((P : ZMod (smallPrime xs outerU i)), (hq i).unit)

def outerUnitMask (P : ℕ) (outerU : List SmallSlot) : ℝ :=
  ∏ i : Fin outerU.length, if P.Coprime outerU[i].value then 1 else 0

theorem smallPrime_product (xs outerU : List SmallSlot) :
    (∏ i, smallPrime xs outerU i) = smallProduct xs * smallProduct outerU := by
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (Fin.prod_univ_fun_getElem xs SmallSlot.value)
    (Fin.prod_univ_fun_getElem outerU SmallSlot.value)

theorem unitFactor_natCast {p : ℕ} [Fact p.Prime] (P : ℕ) :
    unitFactor (P : ZMod p) = if P.Coprime p then 1 else 0 := by
  unfold unitFactor
  by_cases hc : P.Coprime p
  · have hu : IsUnit (P : ZMod p) := (ZMod.isUnit_iff_coprime P p).mpr hc
    exact (ite_eq_left hu).trans (ite_eq_left hc).symm
  · have hu : ¬IsUnit (P : ZMod p) := fun h => hc ((ZMod.isUnit_iff_coprime P p).mp h)
    exact (ite_eq_right hu).trans (ite_eq_right hc).symm

theorem actual_productTest_eq (d : Decomposition) (D P q : ℕ)
    (outerU xs : List SmallSlot) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hv : ∀ i : Fin xs.length, IsUnit (v : ZMod xs[i].value))
    (hA : ∀ i : Fin xs.length,
      IsUnit (coefficientDenominator D outerU xs xs[i].value : ZMod xs[i].value))
    (hq : ∀ i, IsUnit (q : ZMod (smallPrime xs outerU i))) :
    productTest (smallPrime xs outerU) (smallRetained xs outerU)
      (fun i => residueTransform d (smallPrime xs outerU i))
      (smallCoefficients D outerU xs v hv hA) (smallResidues P q xs outerU hq) =
    diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs * outerUnitMask P outerU := by
  let (i : Fin xs.length) : Fact xs[i].value.Prime :=
    inferInstanceAs (Fact (smallPrime xs outerU (.inl i)).Prime)
  unfold productTest
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · change (∏ i : Fin xs.length,
      transformFactor (residueTransform d xs[i].value)
        (coefficientUnit v (coefficientDenominator D outerU xs xs[i].value) (hv i) (hA i))
        (hq (.inl i)).unit (P : ZMod xs[i].value)) = _
    unfold diagonalSmallMultiplier
    rw [← Fin.prod_univ_fun_getElem]
    apply Finset.prod_congr rfl
    intro i hi
    exact (diagonal_factor_eq_transformFactor d D P q outerU xs v
      (small_dvd_smallProduct (List.getElem_mem i.isLt)) (hv i) (hA i) (hq (.inl i))).symm
  · unfold outerUnitMask
    apply Finset.prod_congr rfl
    intro i hi
    exact unitFactor_natCast (p := smallPrime xs outerU (.inr i)) P

theorem outerUnitMask_eq_one (P : ℕ) (outerU : List SmallSlot)
    (hP : ∀ i : Fin outerU.length, IsUnit (P : ZMod outerU[i].value)) :
    outerUnitMask P outerU = 1 := by
  have hc (i : Fin outerU.length) := (ZMod.isUnit_iff_coprime _ _).mp (hP i)
  unfold outerUnitMask
  apply Finset.prod_eq_one
  intro i hi
  exact ite_eq_left (hc i)

theorem actual_productTest_eq_of_outer_units (d : Decomposition) (D P q : ℕ)
    (outerU xs : List SmallSlot) (v : ℤ)
    [∀ i, Fact (smallPrime xs outerU i).Prime]
    (hv : ∀ i : Fin xs.length, IsUnit (v : ZMod xs[i].value))
    (hA : ∀ i : Fin xs.length,
      IsUnit (coefficientDenominator D outerU xs xs[i].value : ZMod xs[i].value))
    (hq : ∀ i, IsUnit (q : ZMod (smallPrime xs outerU i)))
    (hP : ∀ i : Fin outerU.length, IsUnit (P : ZMod outerU[i].value)) :
    productTest (smallPrime xs outerU) (smallRetained xs outerU)
      (fun i => residueTransform d (smallPrime xs outerU i))
      (smallCoefficients D outerU xs v hv hA) (smallResidues P q xs outerU hq) =
    diagonalSmallMultiplier d (D*halfProduct P outerU) v q xs := by
  rw [actual_productTest_eq, outerUnitMask_eq_one P outerU hP, mul_one]

end Ostmann.Arithmetic.DiagonalSmallResidueNorm

end

end OAI
