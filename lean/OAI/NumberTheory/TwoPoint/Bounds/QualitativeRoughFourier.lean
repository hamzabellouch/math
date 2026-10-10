import OAI.NumberTheory.TwoPoint.Bounds.QualitativePrimeScale
import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveBoundary
import OAI.NumberTheory.TwoPoint.Bounds.RoughCutoffProbability
import OAI.NumberTheory.TwoPoint.Bounds.WeightedRoughFourier

namespace OAI

/-! The qualitative rough multiplier, with arbitrary bounded complex
coefficients, obtained directly from the finite four-form sieve. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

lemma rpow_neg_hundred_le_qualitative_rate (B : ℝ) (hB : 1 ≤ B)
    (hlog : 1 ≤ Real.log B) (k : ℕ) (hk : k ≤ 100) :
    B ^ (-100 : ℝ) ≤ (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ k := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hA : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have hAB : B ^ (9999 / 10000 : ℝ) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB
      (show (9999 / 10000 : ℝ) ≤ 1 by norm_num)
  have hi : B⁻¹ ≤ Real.log B / B ^ (9999 / 10000 : ℝ) := by
    calc
      _ ≤ (B ^ (9999 / 10000 : ℝ))⁻¹ := inv_anti₀ hA hAB
      _ ≤ _ := by
        change (B ^ (9999 / 10000 : ℝ))⁻¹ ≤
          Real.log B * (B ^ (9999 / 10000 : ℝ))⁻¹
        nlinarith only [hlog, inv_pos.mpr hA]
  calc
    _ ≤ B ^ (-(k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hB (by
      have hk' : (k : ℝ) ≤ 100 := by exact_mod_cast hk
      linarith only [hk'])
    _ = (B⁻¹) ^ k := by
      rw [show -(k : ℝ) = (-1 : ℝ) * k by ring,
        Real.rpow_mul_natCast hBp.le, Real.rpow_neg_one]
    _ ≤ _ := pow_le_pow_left₀ (inv_nonneg.mpr hBp.le) hi k

/-- The manuscript qualitative multiplier estimate.  Its fourth moment
has only four logarithmic factors, which is stronger than the six needed
in the analytic transfer. -/
theorem PrimeReciprocalInput.qualitative_rough_fourier (hM : PrimeReciprocalInput) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (D h : ℕ), (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D → 0 < h →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      (∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤
        U * (Real.log B / B ^ (9999 / 10000 : ℝ))) ∧
      (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
        V / (D : ℝ) * (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ 4 := by
  obtain ⟨C, hC, hprime⟩ := hM.qualitative_scale
  let U := Real.exp C * 100300 + 2
  let V := Real.exp (4 * C + 6) * 100300 ^ 4 + 2
  refine ⟨U, V, by dsimp [U]; positivity, by dsimp [V]; positivity, ?_⟩
  filter_upwards [hprime, eventually_qualitativeSieveParameters,
    eventually_ge_atTop (Real.exp 1)] with B hp hpar hB
  intro D h hD hh Z c hZ hc
  have hB₁ : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB₁
  have hDp : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  let : NeZero D := ⟨by exact_mod_cast hDp.ne'⟩
  let P := qualitativeSievePrimes B
  let X := qualitativeSieveLogCutoff B
  let Y := Real.exp X
  let r := qualitativeSieveHalfOrder B
  let q := Real.log B / B ^ (9999 / 10000 : ℝ)
  have hX : 0 < X := zero_lt_one.trans_le hpar.cutoff_one
  have hY : 0 ≤ Y := (Real.exp_pos _).le
  have hP (p : ℕ) (hp : p ∈ P) : Nat.Prime p := sievePrimesUpTo_prime Y p hp
  have hmax (p : ℕ) (hp : p ∈ P) : (p : ℝ) ≤ Y := sievePrimesUpTo_le Y hY p hp
  have hcard : (P.card : ℝ) ≤ Y := sievePrimesUpTo_card_le Y hY
  have hlo : Real.log X - C ≤ ∑ p ∈ P, 1 / (p : ℝ) := by
    have ht := (abs_le.mp hp.1).1
    change -C ≤ (∑ p ∈ P, 1 / (p : ℝ)) - Real.log X at ht
    linarith only [ht]
  have hup : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 * Real.log B := by
    have ht := hp.2
    change (∑ p ∈ P, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log B at ht
    linarith [hpar.log_one]
  have he₁ := qualitative_sieve_boundary_cost B hpar hBp 1 Y P.card D
    zero_le_one (by norm_num) hY (Nat.cast_nonneg _) hcard le_rfl hD
  have he₃ := qualitative_sieve_boundary_cost B hpar hBp 3 Y P.card D
    (by norm_num) le_rfl hY (Nat.cast_nonneg _) hcard le_rfl hD
  have hprob₁ := rough_interval_probability_cutoff P hP D D r B C X Y hB₁ hX hY
    hmax hlo hup hpar.nextOrder_large
  have hprob₄ := rough_cube_probability_cutoff P hP (D, D, D) D r B C X Y hB₁ hX hY
    hmax hlo hp.2 hpar.nextOrder_large
  have hsmall₁ : B ^ (-100 : ℝ) ≤ q := by
    simpa only [pow_one] using rpow_neg_hundred_le_qualitative_rate B hB₁ hpar.log_one 1 (by norm_num)
  have hsmall₄ : B ^ (-100 : ℝ) ≤ q ^ 4 :=
    rpow_neg_hundred_le_qualitative_rate B hB₁ hpar.log_one 4 (by norm_num)
  have hinv : 1 / X ≤ 100300 * q := by
    calc
      _ ≤ 100300 * Real.log B / B ^ (9999 / 10000 : ℝ) := hpar.inverse_cutoff
      _ = _ := by dsimp [q]; ring
  have hmain₁ : Real.exp C / X ≤ (Real.exp C * 100300) * q := by
    convert mul_le_mul_of_nonneg_left hinv (Real.exp_pos C).le using 1 <;> ring
  have hmain₄ : Real.exp (4 * C + 6) / X ^ 4 ≤
      (Real.exp (4 * C + 6) * 100300 ^ 4) * q ^ 4 := by
    have ht := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ 1 / X) hinv 4) (Real.exp_pos (4 * C + 6)).le
    convert ht using 1 <;> ring
  have hzsmall : ∀ z ∈ Z, D ≤ z ∧ z < D + D ∧ avoidsPrimeSet P z := by
    intro z hz
    exact ⟨(hZ z hz).1, (hZ z hz).2.1,
      (hZ z hz).2.2.qualitativeSieve hBp⟩
  have hb := weightedRoughFourier_bounds_of_sieve P Z c D h hh (U * q) (V * q ^ 4)
    hzsmall hc (hprob₁.trans (by dsimp [U]; nlinarith only [hmain₁, he₁, hsmall₁]))
    (hprob₄.trans (by dsimp [V]; nlinarith only [hmain₄, he₃, hsmall₄]))
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  ring

end TwoPointCorrelations

end OAI
