import OAI.NumberTheory.JointDickman.Counting.TiltedCoefficient
import OAI.NumberTheory.JointDickman.Amplification.LogProductBounds

namespace OAI

/-! # The Euler-product cost of an exponential prime-count tilt -/

namespace JointDickman

open Finset

noncomputable def tiltPrimeReciprocalMass (P Z : ℕ) (Q : Finset ℕ) : ℝ :=
  ∑ p ∈ (sievePrimes Z).filter (fun p => P < p ∧ p ∈ Q), 1 / (p : ℝ)

noncomputable def tiltedSieveDensity (P Z : ℕ) (Q : Finset ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ sievePrimes Z, (1 - (1 - tiltedSieveTheta P Q s p) / p)

theorem tilted_sieve_density_bound (P Z : ℕ) (Q : Finset ℕ) {s : ℝ}
    (hs : Real.exp s ≤ 2) :
    tiltedSieveDensity P Z Q s ≤ roughSieveDensity P Z *
      Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4) := by
  classical
  let S := sievePrimes Z
  let x := fun p => (1 - tiltedSieveTheta P Q s p) / (p : ℝ)
  let y := roughSieveRate P
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp h).1).2
  have hx (p : ℕ) (h : p ∈ S) : 0 ≤ x p ∧ x p ≤ 1 / 2 := by
    have htheta := tiltedSieveTheta_bounds P Q hs p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    dsimp [x]
    constructor
    · exact div_nonneg (by linarith) hp0.le
    · apply (div_le_iff₀ hp0).mpr
      linarith
  have hy (p : ℕ) (h : p ∈ S) : 0 ≤ y p ∧ y p ≤ 1 / 2 := by
    have hb := roughSieveRate_bounds P p (hp p h)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    exact ⟨hb.1, hb.2.1.trans (one_div_le_one_div_of_le (by norm_num) hp2)⟩
  have hquad (f : ℕ → ℝ) (hf : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ 1 / (p : ℝ)) :
      ∑ p ∈ S, f p ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ S, 1 / (p : ℝ) ^ 2 := by
        apply sum_le_sum
        intro p h
        simpa only [one_div_pow] using pow_le_pow_left₀ (hf p h).1 (hf p h).2 2
      _ ≤ 1 := by
        simpa using sum_reciprocal_square_tail S (by norm_num : (1 : ℕ) ≠ 0)
          (fun p h => (hp p h).one_lt)
  have hxq := hquad x (fun p h => ⟨(hx p h).1, by
    dsimp [x]
    exact div_le_div_of_nonneg_right (by linarith [(tiltedSieveTheta_bounds P Q hs p).1]) (Nat.cast_nonneg p)⟩)
  have hyq := hquad y (fun p h => ⟨(hy p h).1, (roughSieveRate_bounds P p (hp p h)).2.1⟩)
  have hxe := finite_log_product_error S x hx
  have hye := finite_log_product_error S y hy
  have hlin : (∑ p ∈ S, y p) - (∑ p ∈ S, x p) =
      ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q := by
    rw [← sum_sub_distrib]
    unfold tiltPrimeReciprocalMass
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro p h
    by_cases hP : p ≤ P
    · have hn : ¬P < p := by omega
      simp [x, y, roughSieveRate, roughSieveTheta, tiltedSieveTheta, hP, hn]
    · have hP' : P < p := by omega
      by_cases hQ : p ∈ Q <;>
        simp [x, y, roughSieveRate, roughSieveTheta, tiltedSieveTheta, tiltedPrimeWeight, hP, hP', hQ]
      ring
  have hlog : Real.log (∏ p ∈ S, (1 - x p)) ≤
      Real.log (∏ p ∈ S, (1 - y p)) +
        ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4 := by
    have hxe' := (abs_le.mp hxe).2
    have hye' := (abs_le.mp hye).1
    linarith
  have hxprod : 0 < ∏ p ∈ S, (1 - x p) :=
    prod_pos (fun p h => by linarith [(hx p h).2])
  have hyprod : 0 < ∏ p ∈ S, (1 - y p) :=
    prod_pos (fun p h => by linarith [(hy p h).2])
  calc
    _ = Real.exp (Real.log (∏ p ∈ S, (1 - x p))) := (Real.exp_log hxprod).symm
    _ ≤ Real.exp (Real.log (∏ p ∈ S, (1 - y p)) +
        ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [add_assoc, Real.exp_add, Real.exp_log hyprod]; rfl

end JointDickman

end OAI
