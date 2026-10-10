import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticResidueSplit

namespace OAI

/-! # Agreement of the residue split with integer reversal -/

namespace Ostmann

theorem intCast_frequency_zero_iff (s a : ℤ) :
    (a : ZMod s.natAbs) = 0 ↔ s ∣ a := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]

theorem ArithmeticResidueSplit.numerator_integer {Q : ℕ} (d : ArithmeticResidueSplit Q)
    (x : (ZMod Q)ˣ) (XL XR CL CR ML MR : ℤ)
    (hL : d.leftFactor = (XR * CR : ℤ))
    (hR : d.rightFactor = (XL * CL : ℤ))
    (hML : (x : ZMod Q) = ML) (hMR : (d.parentProduct / x : (ZMod Q)ˣ) = (MR : ZMod Q)) :
    d.numerator x = (d.frequencies.left * (XR * CR * MR) -
      d.frequencies.right * (XL * CL * ML) : ℤ) := by
  simp only [ArithmeticResidueSplit.numerator, hL, hR, hML, hMR,
    Int.cast_sub, Int.cast_mul]
  ring

/-- The frequency-divisibility test in the residue evaluator is precisely
the integer test, including either sign of the frequency. -/
theorem ArithmeticResidueSplit.frequency_test_integer {Q : ℕ}
    (d : ArithmeticResidueSplit Q) (x : (ZMod Q)ˣ) (N : ℤ)
    (hN : d.numerator x = N) :
    d.reduce (d.numerator x) = 0 ↔ d.frequencies.root ∣ N := by
  rw [hN, ArithmeticResidueSplit.reduce, map_intCast]
  exact intCast_frequency_zero_iff _ _

noncomputable def ArithmeticResidueSplit.pivot {R M : ℕ}
    (d : ArithmeticResidueSplit (R * M)) (hsR : d.frequencies.root.natAbs ∣ R)
    (U : (ZMod M)ˣ) (x : (ZMod (R * M))ˣ) : ZMod M :=
  frequencyQuotient R M d.frequencies.root hsR (d.numerator x) * ↑U⁻¹

/-- The residue evaluator reconstructs the same pivot as the original
integer formula, at the remaining precision. -/
theorem ArithmeticResidueSplit.pivot_integer {R M : ℕ} [NeZero M]
    (d : ArithmeticResidueSplit (R * M)) (hsR : d.frequencies.root.natAbs ∣ R)
    (U : (ZMod M)ˣ) (x : (ZMod (R * M))ˣ) (u p : ℤ)
    (hU : (U : ZMod M) = u)
    (hN : d.numerator x = (d.frequencies.root * u * p : ℤ)) :
    d.pivot hsR U x = p := by
  rw [ArithmeticResidueSplit.pivot, hN]
  simpa only [Int.cast_mul] using frequencyQuotient_reversal R M d.frequencies.root
    d.frequency_ne_zero hsR u p U hU

end Ostmann

end OAI
