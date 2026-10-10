import OAI.NumberTheory.Ostmann.Construction.CompensatedAdaptiveCoefficients
import OAI.NumberTheory.Ostmann.Construction.AdaptivePivotSupport
import OAI.NumberTheory.Ostmann.Arithmetic.SequentialActualSupport

namespace OAI

/-! # Actual integral histories pass the constructed adaptive split tests -/

namespace Ostmann

open scoped Classical

noncomputable def compensatedAdaptiveResidueSplit (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1) : ArithmeticResidueSplit (R ^ (k + 2)) where
  frequencies := D.frequencies ⟨past.length, hj⟩
  frequency_ne_zero := hs _
  frequency_dvd := (hsR _).trans (dvd_pow_self R (by omega))
  leftFactor := (compensatedAdaptiveCoefficients n (R ^ (k + 2)) D U total past).1
  rightFactor := (compensatedAdaptiveCoefficients n (R ^ (k + 2)) D U total past).2
  parentProduct := splitPrefixParent n total past

noncomputable def compensatedAdaptiveData (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ) :
    Option (ArithmeticSplitData (R ^ (k + 2))) :=
  if hj : past.length < 2 ^ n - 1 then
    (compensatedAdaptiveResidueSplit n R k D U hs hsR total past hj).toData
  else none

theorem compensatedAdaptiveData_frequencies (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (hj : past.length < 2 ^ n - 1) (d : ArithmeticSplitData (R ^ (k + 2)))
    (hd : compensatedAdaptiveData n R k D U hs hsR total past = some d) :
    d.hasFrequencies (D.frequencies ⟨past.length, hj⟩) := by
  rw [compensatedAdaptiveData, dite_eq_left hj] at hd
  exact ArithmeticResidueSplit.toData_frequencies _ _ hd

/-- A valid actual history passes every test. The coefficients in that test
were constructed using only the root product and the preceding split prefix. -/
theorem compensatedAdaptiveData_actual_test (n R k : ℕ)
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.compensatedValid D U)
    (j : ℕ) (hj : j < 2 ^ n - 1) :
    singleArithmeticSplitTest
      (compensatedAdaptiveData n R k D U hs hsR (treeLeafProduct n a.residue)
        ((actualSplitValues n a.residue).take j).reverse)
      ((actualSplitValues n a.residue).getD j 1) := by
  let total := treeLeafProduct n a.residue
  let past := ((actualSplitValues n a.residue).take j).reverse
  have hlen : past.length = j := by
    simp only [past, List.length_reverse, List.length_take, actualSplitValues_length,
      min_eq_left (Nat.le_of_lt hj)]
  have hj' : past.length < 2 ^ n - 1 := by omega
  let d := compensatedAdaptiveResidueSplit n R k D U hs hsR total past hj'
  change singleArithmeticSplitTest (compensatedAdaptiveData n R k D U hs hsR total past) _
  rw [compensatedAdaptiveData, dite_eq_left hj', singleArithmeticSplitTest_toData]
  change d.support _
  let i : Fin (2 ^ n - 1) := ⟨past.length, hj'⟩
  let c := (actualChildProducts n a.residue).getD j (1, 1)
  have hc := actualChildProducts_from_prefix n a.residue j hj
  have hcL : c.1 = (actualSplitValues n a.residue).getD j 1 := congrArg Prod.fst hc
  have hcP : splitPrefixParent n total past = c.1 * c.2 := by
    rw [show c = ((actualSplitValues n a.residue).getD j 1,
      splitPrefixParent n total past / (actualSplitValues n a.residue).getD j 1) from hc]
    dsimp only
    rw [mul_comm, div_mul_cancel]
  have hcoeff := compensatedAdaptiveCoefficients_reduce n R k D U hU hdepth hs hsR a ha
    total past (a.matches_actual j (Nat.le_of_lt hj)) hj'
  have hci := treeIntegerResidues_child (R ^ (k + 2)) n a.bulk a.residue a.compatible j
  have hL : (c.1 : ZMod (R ^ (k + 2))) = a.leftProduct i := by
    simpa only [c, SampledPivotHistory.leftProduct, i, hlen] using hci.1
  have hR : (c.2 : ZMod (R ^ (k + 2))) = a.rightProduct i := by
    simpa only [c, SampledPivotHistory.rightProduct, i, hlen] using hci.2
  apply d.support_of_reduced_integer_data _
    (D.leftCoefficient a.pivots i) (D.rightCoefficient a.pivots i)
    (a.leftProduct i) (a.rightProduct i) (U i * a.pivots i)
    (ZMod.unitsMap d.frequency_dvd c.1) (ZMod.unitsMap d.frequency_dvd c.2)
  · exact hcoeff.1
  · exact hcoeff.2
  · change ZMod.unitsMap d.frequency_dvd (splitPrefixParent n total past) = _
    rw [hcP, map_mul]
  · rw [← hcL]
  · change ZMod.castHom d.frequency_dvd _ (c.1 : ZMod (R ^ (k + 2))) = _
    rw [hL, map_intCast]
  · change ZMod.castHom d.frequency_dvd _ (c.2 : ZMod (R ^ (k + 2))) = _
    rw [hR, map_intCast]
  · exact (ha.2 i).1
  · exact (ha.2 i).2
  · change (D.frequencies i).left * D.leftCoefficient a.pivots i * a.rightProduct i -
        (D.frequencies i).right * D.rightCoefficient a.pivots i * a.leftProduct i =
          (D.frequencies i).root * (U i * a.pivots i)
    simpa only [mul_assoc] using ha.1 i

/-- The entire original residue tuple remains in the arithmetic support. -/
theorem compensatedAdaptiveData_actual_support (n R k : ℕ) [NeZero (R ^ (k + 2))]
    (D : PivotDependencyScheme (2 ^ n - 1)) (U : Fin (2 ^ n - 1) → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ))
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (a : SampledPivotHistory n (R ^ (k + 2))) (ha : a.compensatedValid D U) :
    singleArithmeticLeafSupport n (compensatedAdaptiveData n R k D U hs hsR) a.residue = 1 := by
  apply singleArithmeticLeafSupport_eq_one_of_actual_tests
  exact compensatedAdaptiveData_actual_test n R k D U hU hdepth hs hsR a ha

end Ostmann

end OAI
