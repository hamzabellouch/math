import OAI.NumberTheory.Ostmann.Characters.CRTFourier
import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallKernelQuadraticSum

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

noncomputable def centeredDensity {q : ℕ} (S : Finset (ZMod q)) (x : ZMod q) : ℝ :=
  (if x ∈ S then 1 else 0) - (S.card : ℝ) / q

noncomputable def densityFourier {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  (Real.sqrt (q : ℝ) : ℂ) * additiveFourier f a

theorem centeredDensity_abs_le {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (x : ZMod q) :
    |centeredDensity S x| ≤ 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hcard : (S.card : ℝ) ≤ q := by
    exact_mod_cast (show S.card ≤ q by simpa using Finset.card_le_card (Finset.subset_univ S))
  have hσ : (S.card : ℝ) / q ≤ 1 := (div_le_one hq).mpr hcard
  have hσ0 : 0 ≤ (S.card : ℝ) / q := by positivity
  unfold centeredDensity
  split <;> rw [abs_le] <;> constructor <;> linarith

theorem centeredDensity_sum {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ∑ x : ZMod q, centeredDensity S x = 0 := by
  classical
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold centeredDensity
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ x : ZMod q, if x ∈ S then (1 : ℝ) else 0) = S.card := by simp
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp
  ring

theorem densityFourier_energy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) = ∑ x : ZMod q, ‖f x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [densityFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, additiveFourier_parseval, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem densityFourier_energy_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : (∑ a : ZMod q, ‖densityFourier f a‖ ^ 2) ≤ q := by
  rw [densityFourier_energy]
  calc
    _ ≤ ∑ _x : ZMod q, (1 : ℝ) := Finset.sum_le_sum (fun x _ => by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hf x) 2)
    _ = _ := by simp

theorem densityFourier_centered_zero {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    densityFourier (fun x => (centeredDensity S x : ℂ)) 0 = 0 := by
  simp only [densityFourier, additiveFourier_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have hsum : (∑ x : ZMod q, (centeredDensity S x : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, centeredDensity_sum, Complex.ofReal_zero]
  rw [hsum, mul_zero, mul_zero]

theorem densityFourier_centered_energy {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    (∑ a : ZMod q, ‖densityFourier (fun x => (centeredDensity S x : ℂ)) a‖ ^ 2) ≤ q := by
  apply densityFourier_energy_le
  intro x
  simpa only [Complex.norm_real, Real.norm_eq_abs] using centeredDensity_abs_le S x

/-- Probability-normalized CRT Fourier factorization remains exact after
multiplication by the square root of the modulus. -/
theorem densityFourier_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (f : ZMod m → ℂ) (g : ZMod n → ℂ) (u : ZMod (m * n)) :
    densityFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      g ((ZMod.chineseRemainder h) x).2) u =
      densityFourier f ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) u).1) *
      densityFourier g ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) u).2) := by
  simp only [densityFourier, additiveFourier_crt h f g u, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]
  ring

/-- Each local centered Fourier transform vanishes at zero. The CRT product
therefore vanishes at every nonunit of the composite modulus. -/
theorem densityFourier_crt_nonunit {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (f : ZMod m → ℂ) (g : ZMod n → ℂ)
    (hf : ∀ x, ¬IsUnit x → densityFourier f x = 0)
    (hg : ∀ x, ¬IsUnit x → densityFourier g x = 0)
    (u : ZMod (m * n)) (hu : ¬IsUnit u) :
    densityFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      g ((ZMod.chineseRemainder h) x).2) u = 0 := by
  rw [densityFourier_crt]
  by_cases h₁ : IsUnit ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) u).1)
  · have h₂ : ¬IsUnit ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) u).2) := by
      intro h₂
      have ha := isUnit_of_mul_isUnit_right h₁
      have hb := isUnit_of_mul_isUnit_right h₂
      obtain ⟨a, ha⟩ := ha.exists_right_inv
      obtain ⟨b, hb⟩ := hb.exists_right_inv
      have he : IsUnit ((ZMod.chineseRemainder h) u) :=
        IsUnit.of_mul_eq_one (a, b) (Prod.ext ha hb)
      have hh := he.map (ZMod.chineseRemainder h).symm.toMonoidHom
      change IsUnit ((ZMod.chineseRemainder h).symm ((ZMod.chineseRemainder h) u)) at hh
      exact hu (by simpa only [RingEquiv.symm_apply_apply] using hh)
    rw [hg _ h₂, mul_zero]
  · rw [hf _ h₁, zero_mul]

/-- This supplies the local hypotheses for every prime factor of `L`. -/
theorem densityFourier_centered_prime_nonunit {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (x : ZMod p) (hx : ¬IsUnit x) :
    densityFourier (fun y => (centeredDensity S y : ℂ)) x = 0 := by
  have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hx
  rw [hx0, densityFourier_centered_zero]

end Ostmann

end OAI
