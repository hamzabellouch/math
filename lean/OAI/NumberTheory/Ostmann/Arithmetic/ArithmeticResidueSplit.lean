import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSplitTreeSupport
import OAI.NumberTheory.Ostmann.Arithmetic.ResidueQuotient

namespace OAI

/-! # Constructing the support data from an actual residue numerator -/

namespace Ostmann

open scoped Classical

/-- The two coefficients contain the current giant and its nonbulk
factors. They are allowed to fail the required unit tests. -/
structure ArithmeticResidueSplit (Q : ℕ) where
  frequencies : NodeFrequencies
  frequency_ne_zero : frequencies.root ≠ 0
  frequency_dvd : frequencies.root.natAbs ∣ Q
  leftFactor : ZMod Q
  rightFactor : ZMod Q
  parentProduct : (ZMod Q)ˣ

def ArithmeticResidueSplit.reduce {Q : ℕ} (d : ArithmeticResidueSplit Q) :
    ZMod Q →+* ZMod d.frequencies.root.natAbs :=
  ZMod.castHom d.frequency_dvd _

def ArithmeticResidueSplit.numerator {Q : ℕ} (d : ArithmeticResidueSplit Q)
    (x : (ZMod Q)ˣ) : ZMod Q :=
  (d.frequencies.left : ZMod Q) * d.leftFactor * ↑(d.parentProduct / x) -
    (d.frequencies.right : ZMod Q) * d.rightFactor * ↑x

def ArithmeticResidueSplit.support {Q : ℕ} (d : ArithmeticResidueSplit Q)
    (x : (ZMod Q)ˣ) : Prop :=
  IsUnit (d.reduce d.leftFactor) ∧ IsUnit (d.reduce d.rightFactor) ∧
    d.reduce (d.numerator x) = 0

noncomputable def ArithmeticResidueSplit.toData {Q : ℕ} (d : ArithmeticResidueSplit Q) :
    Option (ArithmeticSplitData Q) :=
  if hL : IsUnit (d.reduce d.leftFactor) then
    if hR : IsUnit (d.reduce d.rightFactor) then
      some {
        frequency := d.frequencies.root
        frequency_ne_zero := d.frequency_ne_zero
        frequency_dvd := d.frequency_dvd
        leftFrequency := d.frequencies.left
        rightFrequency := d.frequencies.right
        leftFactor := hL.unit
        rightFactor := hR.unit
        parentProduct := ZMod.unitsMap d.frequency_dvd d.parentProduct }
    else none
  else none

theorem ArithmeticResidueSplit.toData_frequencies {Q : ℕ}
    (d : ArithmeticResidueSplit Q) (e : ArithmeticSplitData Q)
    (h : d.toData = some e) : e.hasFrequencies d.frequencies := by
  unfold ArithmeticResidueSplit.toData at h
  split_ifs at h with hL hR
  · cases Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩

theorem ArithmeticResidueSplit.toData_test {Q : ℕ}
    (d : ArithmeticResidueSplit Q) (x : (ZMod Q)ˣ) :
    (∃ e, d.toData = some e ∧ e.test x) ↔ d.support x := by
  have hquot : ZMod.unitsMap d.frequency_dvd d.parentProduct /
      ZMod.unitsMap d.frequency_dvd x = ZMod.unitsMap d.frequency_dvd (d.parentProduct / x) :=
    (map_div (ZMod.unitsMap d.frequency_dvd) _ _).symm
  unfold ArithmeticResidueSplit.toData ArithmeticResidueSplit.support
  split_ifs with hL hR
  · simp only [Option.some.injEq, hL, hR, true_and]
    constructor
    · rintro ⟨e, rfl, h⟩
      dsimp only [ArithmeticSplitData.test] at h
      rw [hquot] at h
      simpa only [ArithmeticResidueSplit.numerator, ArithmeticResidueSplit.reduce,
        map_sub, map_mul, map_intCast, sub_eq_zero, Units.val_mul, IsUnit.unit_spec,
        ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, mul_assoc] using h
    · intro h
      refine ⟨_, rfl, ?_⟩
      dsimp only [ArithmeticSplitData.test]
      rw [hquot]
      simpa only [ArithmeticResidueSplit.numerator, ArithmeticResidueSplit.reduce,
        map_sub, map_mul, map_intCast, sub_eq_zero, Units.val_mul, IsUnit.unit_spec,
        ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, mul_assoc] using h
  · simp [hR]
  · simp [hL]

noncomputable def arithmeticResiduePairData {Q : ℕ}
    (d e : ArithmeticResidueSplit Q) : Option (ArithmeticSplitData Q × ArithmeticSplitData Q) :=
  match d.toData, e.toData with
  | some d', some e' => some (d', e')
  | _, _ => none

theorem arithmeticResiduePairData_test {Q : ℕ}
    (d e : ArithmeticResidueSplit Q) (x : (ZMod Q)ˣ) :
    arithmeticPairSplitTest (arithmeticResiduePairData d e) x ↔
      d.support x ∧ e.support x := by
  rw [← d.toData_test x, ← e.toData_test x]
  unfold arithmeticResiduePairData
  cases hd : d.toData <;> cases he : e.toData <;>
    simp [arithmeticPairSplitTest]

theorem arithmeticResiduePairData_frequencies {Q : ℕ}
    (d e : ArithmeticResidueSplit Q) (d' e' : ArithmeticSplitData Q)
    (h : arithmeticResiduePairData d e = some (d', e')) :
    d'.hasFrequencies d.frequencies ∧ e'.hasFrequencies e.frequencies := by
  unfold arithmeticResiduePairData at h
  cases hd : d.toData <;> cases he : e.toData <;> simp only [hd, he] at h
  · cases h
  · cases h
  · cases h
  · cases Option.some.inj h
    exact ⟨d.toData_frequencies _ hd, e.toData_frequencies _ he⟩

end Ostmann

end OAI
