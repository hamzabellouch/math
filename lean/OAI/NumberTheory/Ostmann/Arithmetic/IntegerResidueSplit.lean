import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticResidueSplit
import OAI.NumberTheory.Ostmann.Arithmetic.SingleHistorySupport

namespace OAI

/-! # Exact integer reconstruction implies the adaptive residue test -/

namespace Ostmann

open scoped Classical

theorem intCast_frequency_zero (s : ℤ) : (s : ZMod s.natAbs) = 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd s s.natAbs).mpr
  exact Int.natCast_dvd.mpr (dvd_refl _)

theorem intCast_isUnit_of_coprime_frequency (a s : ℤ) (ha : IsCoprime a s) :
    IsUnit (a : ZMod s.natAbs) := by
  have h := ha.map (Int.castRingHom (ZMod s.natAbs))
  simpa only [Int.coe_castRingHom, intCast_frequency_zero, isCoprime_zero_right] using h

/-- `A` and `B` contain only the known nonbulk factors. The two variable
products are units in the full modulus, and determine the parent product. -/
def integerResidueSplit {Q : ℕ} (f : NodeFrequencies) (hs : f.root ≠ 0)
    (hdvd : f.root.natAbs ∣ Q) (A B : ℤ) (L R : (ZMod Q)ˣ) : ArithmeticResidueSplit Q where
  frequencies := f
  frequency_ne_zero := hs
  frequency_dvd := hdvd
  leftFactor := (A : ZMod Q)
  rightFactor := (B : ZMod Q)
  parentProduct := L * R

/-- The integrality equation itself supplies the zero-numerator test.
No equidistribution or independence is used in this bridge. -/
theorem integerResidueSplit_support {Q : ℕ} (f : NodeFrequencies)
    (hs : f.root ≠ 0) (hdvd : f.root.natAbs ∣ Q)
    (A B l r P : ℤ) (L R : (ZMod Q)ˣ)
    (hL : (L : ZMod Q) = l) (hR : (R : ZMod Q) = r)
    (hA : IsCoprime A f.root) (hB : IsCoprime B f.root)
    (heq : f.left * A * r - f.right * B * l = f.root * P) :
    (integerResidueSplit f hs hdvd A B L R).support L := by
  have hquot : L * R / L = R := mul_div_cancel_left L R
  constructor
  · change IsUnit (ZMod.cast (A : ZMod Q) : ZMod f.root.natAbs)
    rw [ZMod.cast_intCast hdvd A]
    exact intCast_isUnit_of_coprime_frequency A f.root hA
  constructor
  · change IsUnit (ZMod.cast (B : ZMod Q) : ZMod f.root.natAbs)
    rw [ZMod.cast_intCast hdvd B]
    exact intCast_isUnit_of_coprime_frequency B f.root hB
  · have hrel := congrArg (fun z : ℤ => (z : ZMod f.root.natAbs)) heq
    simp only [Int.cast_sub, Int.cast_mul, intCast_frequency_zero, zero_mul] at hrel
    dsimp only [ArithmeticResidueSplit.reduce, ArithmeticResidueSplit.numerator, integerResidueSplit]
    rw [hquot, hL, hR]
    simp only [← Int.cast_mul, ← Int.cast_sub]
    change (ZMod.cast ((f.left * A * r - f.right * B * l : ℤ) : ZMod Q) :
      ZMod f.root.natAbs) = 0
    rw [ZMod.cast_intCast hdvd]
    simpa only [Int.cast_sub, Int.cast_mul] using hrel

theorem singleArithmeticSplitTest_toData {Q : ℕ} (d : ArithmeticResidueSplit Q)
    (x : (ZMod Q)ˣ) : singleArithmeticSplitTest d.toData x ↔ d.support x := by
  rw [← d.toData_test x]
  cases hd : d.toData <;> simp [singleArithmeticSplitTest]

/-- A valid actual node gives a successful adaptive test after reduction.
The statement remains valid for signed frequencies and reconstructed pivots. -/
theorem integerResidueSplit_test {Q : ℕ} (f : NodeFrequencies)
    (hs : f.root ≠ 0) (hdvd : f.root.natAbs ∣ Q)
    (A B l r P : ℤ) (L R : (ZMod Q)ˣ)
    (hL : (L : ZMod Q) = l) (hR : (R : ZMod Q) = r)
    (hA : IsCoprime A f.root) (hB : IsCoprime B f.root)
    (heq : f.left * A * r - f.right * B * l = f.root * P) :
    singleArithmeticSplitTest (integerResidueSplit f hs hdvd A B L R).toData L := by
  exact (singleArithmeticSplitTest_toData _ _).mpr
    (integerResidueSplit_support f hs hdvd A B l r P L R hL hR hA hB heq)

/-- At a later split only the surviving residues of the previously
reconstructed coefficients are needed. Full-modulus equality is unnecessary. -/
theorem ArithmeticResidueSplit.support_of_reduced_integer_data {Q : ℕ}
    (d : ArithmeticResidueSplit Q) (x : (ZMod Q)ˣ)
    (A B l r P : ℤ) (L R : (ZMod d.frequencies.root.natAbs)ˣ)
    (hA : d.reduce d.leftFactor = A) (hB : d.reduce d.rightFactor = B)
    (hparent : ZMod.unitsMap d.frequency_dvd d.parentProduct = L * R)
    (hx : ZMod.unitsMap d.frequency_dvd x = L)
    (hL : (L : ZMod d.frequencies.root.natAbs) = l)
    (hR : (R : ZMod d.frequencies.root.natAbs) = r)
    (huA : IsCoprime A d.frequencies.root) (huB : IsCoprime B d.frequencies.root)
    (heq : d.frequencies.left * A * r - d.frequencies.right * B * l = d.frequencies.root * P) :
    d.support x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hA]
    exact intCast_isUnit_of_coprime_frequency A d.frequencies.root huA
  · rw [hB]
    exact intCast_isUnit_of_coprime_frequency B d.frequencies.root huB
  · have hrel := congrArg (fun z : ℤ => (z : ZMod d.frequencies.root.natAbs)) heq
    simp only [Int.cast_sub, Int.cast_mul, intCast_frequency_zero, zero_mul] at hrel
    have hquot : ZMod.unitsMap d.frequency_dvd (d.parentProduct / x) = R := by
      rw [map_div, hparent, hx, mul_div_cancel_left]
    have hnum : d.reduce (d.numerator x) =
        (d.frequencies.left : ZMod d.frequencies.root.natAbs) * d.reduce d.leftFactor *
          (ZMod.unitsMap d.frequency_dvd (d.parentProduct / x) : (ZMod d.frequencies.root.natAbs)ˣ) -
        (d.frequencies.right : ZMod d.frequencies.root.natAbs) * d.reduce d.rightFactor *
          (ZMod.unitsMap d.frequency_dvd x : (ZMod d.frequencies.root.natAbs)ˣ) := by
      simp only [ArithmeticResidueSplit.reduce, ArithmeticResidueSplit.numerator,
        map_sub, map_mul, map_intCast, ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe]
    rw [hnum, hA, hB, hquot, hx, hL, hR]
    exact hrel

end Ostmann

end OAI
