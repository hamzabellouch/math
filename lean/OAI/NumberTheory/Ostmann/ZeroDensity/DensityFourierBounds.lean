import OAI.NumberTheory.Ostmann.ZeroDensity.DensityCRTProduct
import OAI.NumberTheory.Ostmann.Characters.AffineAction
import OAI.NumberTheory.Ostmann.Preliminaries.TestFunctions

namespace OAI

/-! # The two local Fourier bounds in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_twice {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (additiveFourier f) a = (q : ℂ)⁻¹ * f (-a) := by
  rw [additiveFourier_apply]
  congr 1
  have hi := additiveFourier_inversion f (-a)
  simpa only [mul_neg] using hi.symm

/-- A prime occurring in exactly one of the divisors costs `q^(-1/2)`. -/
theorem densityFourier_coefficient_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (a : ZMod q) :
    ‖additiveFourier (densityFourier f) a‖ ≤ (Real.sqrt (q : ℝ))⁻¹ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  change ‖additiveFourier (fun x => (Real.sqrt (q : ℝ) : ℂ) * additiveFourier f x) a‖ ≤ _
  rw [additiveFourier_const_mul, additiveFourier_twice, norm_mul, norm_mul, norm_inv,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc
    _ ≤ Real.sqrt (q : ℝ) * ((q : ℝ)⁻¹ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf (-a)) (by positivity)) hs.le
    _ = _ := by field_simp; nlinarith

/-- Unit dilations preserve the local coefficient bound. -/
theorem densityFourier_unit_coefficient_le {q : ℕ} [NeZero q]
    (f : ZMod q → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (a : (ZMod q)ˣ) (u : ZMod q) :
    ‖additiveFourier (fun x => densityFourier f ((a : ZMod q) * x)) u‖ ≤ (Real.sqrt (q : ℝ))⁻¹ := by
  rw [additiveFourier_unit_mul]
  exact densityFourier_coefficient_le f hf _

/-- At a common prime, the product costs only one, by Cauchy--Schwarz. -/
theorem additiveFourier_cross_le_one {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (hf : (∑ x, ‖f x‖ ^ 2) ≤ q)
    (hg : (∑ x, ‖g x‖ ^ 2) ≤ q) (u : ZMod q) :
    ‖additiveFourier (fun x => f x * conj (g x)) u‖ ≤ 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hS : 0 ≤ ∑ x : ZMod q, ‖f x‖ * ‖g x‖ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖f x‖) (fun x => ‖g x‖)
  have he : (∑ x : ZMod q, ‖f x‖ * ‖g x‖) ≤ q := by
    have hb := mul_le_mul hf hg (by positivity : 0 ≤ ∑ x : ZMod q, ‖g x‖ ^ 2) hq.le
    nlinarith
  rw [additiveFourier_apply, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ x : ZMod q, ‖f x‖ * ‖g x‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hq.le)
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro x hx
      simp only [norm_mul, Complex.norm_conj]
      have hn : ‖ZMod.stdAddChar (-(x * u))‖ = 1 := by simp [ZMod.stdAddChar_apply]
      rw [hn, mul_one]
    _ ≤ (q : ℝ)⁻¹ * q := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hq.le)
    _ = 1 := inv_mul_cancel₀ hq.ne'

/-- Conjugation reverses the Fourier frequency. -/
theorem additiveFourier_conj {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (fun x => conj (f x)) a = conj (additiveFourier f (-a)) := by
  simp only [additiveFourier_apply, map_mul, map_sum, map_inv₀, map_natCast,
    stdAddChar_conj, mul_neg, neg_neg]

/-- Unit dilations preserve the counting-measure energy. -/
theorem unit_dilation_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖f ((a : ZMod q) * x)‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 :=
  (Units.mulLeft a).bijective.sum_comp (fun x : ZMod q => ‖f x‖ ^ 2)

/-- The common-prime factor of the original density correlation. -/
theorem densityFourier_unit_cross_le_one {q : ℕ} [NeZero q]
    (f g : ZMod q → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (a b : (ZMod q)ˣ) (u : ZMod q) :
    ‖additiveFourier (fun x => densityFourier f ((a : ZMod q) * x) *
      conj (densityFourier g ((b : ZMod q) * x))) u‖ ≤ 1 := by
  apply additiveFourier_cross_le_one
  · rw [unit_dilation_energy]
    exact densityFourier_energy_le f hf
  · rw [unit_dilation_energy]
    exact densityFourier_energy_le g hg

end Ostmann

end OAI
