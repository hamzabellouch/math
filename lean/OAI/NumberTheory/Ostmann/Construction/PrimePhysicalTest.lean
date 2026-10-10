import OAI.NumberTheory.Ostmann.Construction.RepeatedPhysicalTests

namespace OAI

/-! # The exact physical tests for the two kinds of prime position -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- Degenerate residue sets give the zero normalized test. Thus the energy
bound holds before a balanced-prime restriction is inserted. -/
theorem normalizedResidueIndicator_energy_le {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) :
    (∑ x, ‖normalizedResidueIndicator S x‖ ^ 2) ≤ (p : ℝ) := by
  by_cases hS : S.Nonempty
  · by_cases hSp : S.card < p
    · exact (normalizedResidueIndicator_energy S hS hSp).le
    · have hc : S.card = p := by
        have ht := Finset.card_le_univ S
        rw [ZMod.card] at ht
        omega
      have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
      have hv : residueVariance S = 0 := by
        simp only [residueVariance, residueDensity, hc, div_self hp, sub_self, mul_zero]
      simp only [normalizedResidueIndicator, hv, Real.sqrt_zero, div_zero,
        Complex.ofReal_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
      exact Nat.cast_nonneg p
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [normalizedResidueIndicator, residueVariance, residueDensity, Finset.card_empty,
      Nat.cast_zero, zero_div, zero_mul, Real.sqrt_zero, div_zero, Complex.ofReal_zero,
      norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact Nat.cast_nonneg p

/-- A giant uses the Fourier phase on favorable primes and zero elsewhere;
every other prime position uses the exact normalized residue indicator. -/
noncomputable def primePhysicalTest {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) : ZMod p → ℂ :=
  if giant then
    if favorable then phaseGiantPhysical (normalizedResidueTransform S) else fun _ => 0
  else normalizedResidueIndicator S

theorem primePhysicalTest_sum {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) :
    (∑ x, primePhysicalTest S giant favorable x) = 0 := by
  cases giant <;> cases favorable <;> simp only [primePhysicalTest, Bool.false_eq_true,
    ↓reduceIte, Finset.sum_const_zero, normalizedResidueIndicator_sum,
    phaseGiantPhysical_sum_zero _ (normalizedResidueTransform_zero S)]

theorem primePhysicalTest_energy {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) :
    (∑ x, ‖primePhysicalTest S giant favorable x‖ ^ 2) ≤ (p : ℝ) := by
  cases giant <;> cases favorable
  · exact normalizedResidueIndicator_energy_le S
  · exact normalizedResidueIndicator_energy_le S
  · simp only [primePhysicalTest, ↓reduceIte, Bool.false_eq_true, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact Nat.cast_nonneg p
  · exact phaseGiantPhysical_energy _

theorem primePhysicalTest_bound {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) (x : ZMod p) :
    ‖primePhysicalTest S giant favorable x‖ ≤ Real.sqrt p :=
  localTest_bound_of_energy _ (primePhysicalTest_energy S giant favorable) x

theorem primePhysicalTest_real {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (giant favorable : Bool) (x : ZMod p) :
    (primePhysicalTest S giant favorable x).im = 0 := by
  cases giant <;> cases favorable
  · exact Complex.ofReal_im _
  · exact Complex.ofReal_im _
  · rfl
  · exact phaseGiantPhysical_real _ (normalizedResidueTransform_neg S) x

theorem primePhysicalTest_fourier {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) (b : ZMod p) :
    densityFourier (primePhysicalTest S giant favorable) b =
      if giant then
        if favorable then complexUnitPhase (normalizedResidueTransform S b) else 0
      else normalizedResidueTransform S b := by
  cases giant <;> cases favorable
  · rfl
  · rfl
  · simp only [primePhysicalTest, ↓reduceIte, Bool.false_eq_true, densityFourier,
      additiveFourier_apply, zero_mul, Finset.sum_const_zero, mul_zero]
  · exact phaseGiantPhysical_transform _ _

end Ostmann

end OAI
