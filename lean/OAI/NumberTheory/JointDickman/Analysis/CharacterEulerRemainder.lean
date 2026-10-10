import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterFactorization

namespace OAI

/-! # The linear prime sum in a character Euler logarithm

The nonlinear Euler terms have one absolute summable majorant throughout
Re(s) > 1, independent of both the character and its modulus.
-/
namespace JointDickman
open Complex

noncomputable def primeCharacterLinearSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, characterPrimePower χ s p

noncomputable def primeEulerRemainderConstant : ℝ :=
  ∑' p : Nat.Primes, 2 * (p.val : ℝ)^(-2:ℝ)

theorem primeEulerRemainderConstant_nonneg : 0 ≤ primeEulerRemainderConstant :=
  tsum_nonneg (fun _ => by positivity)

theorem primeCharacterLinearSum_summable {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => characterPrimePower χ s p) := by
  apply Summable.of_norm
  convert! (summable_dirichletSummand χ hs).subtype Nat.Prime using 1

theorem primeCharacterLog_linear_error {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖primeCharacterLog χ s - primeCharacterLinearSum χ s‖ ≤
      primeEulerRemainderConstant := by
  have hsum : Summable (fun p : Nat.Primes => 2*(p.val:ℝ)^(-2:ℝ)) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ) < -1)).subtype Nat.Prime).mul_left 2
  have hpoint (p : Nat.Primes) :
      ‖-Complex.log (1-characterPrimePower χ s p)-characterPrimePower χ s p‖ ≤
        2*(p.val:ℝ)^(-2:ℝ) := by
    have hhalf : ‖characterPrimePower χ s p‖ ≤ 1/2 :=
      (characterPrimePower_norm_le χ p).trans (Complex.norm_prime_cpow_le_one_half p hs)
    have hnorm : ‖characterPrimePower χ s p‖ ≤ (p.val:ℝ)^(-1:ℝ) := by
      calc
        _ ≤ ‖(p.val:ℂ)^(-s)‖ := characterPrimePower_norm_le χ p
        _ = (p.val:ℝ)^(-s.re) := by
          rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast p.property.one_le) (by linarith)
    have hlog := complex_log_error_bound (by norm_num : (1/2:ℝ) < 1)
      (show ‖-characterPrimePower χ s p‖ ≤ 1/2 by simpa using hhalf)
    have he : -Complex.log (1-characterPrimePower χ s p)-characterPrimePower χ s p =
        -(Complex.log (1+(-characterPrimePower χ s p))-(-characterPrimePower χ s p)) := by
      simp only [sub_eq_add_neg]; ring
    rw [he, norm_neg]
    calc
      _ ≤ ‖characterPrimePower χ s p‖^2/(1-(1/2:ℝ)) := by simpa using hlog
      _ ≤ ((p.val:ℝ)^(-1:ℝ))^2/(1-(1/2:ℝ)) := by gcongr
      _ = 2*(p.val:ℝ)^(-2:ℝ) := by
        rw [←Real.rpow_mul_natCast (by positivity)]
        norm_num
        ring
  rw [primeCharacterLog, primeCharacterLinearSum,
    ←Summable.tsum_sub (primeCharacterLog_summable χ hs)
      (primeCharacterLinearSum_summable χ hs)]
  have herror := hsum.of_norm_bounded hpoint
  exact (norm_tsum_le_tsum_norm herror.norm).trans
    (herror.norm.tsum_le_tsum hpoint hsum)

theorem primeCharacterLog_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    (primeCharacterLog χ s).re = Real.log ‖χ.LFunction s‖ := by
  rw [←primeCharacterLog_exp χ hs, Complex.norm_exp, Real.log_exp]

theorem primeCharacterLinearSum_re_error {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    |(primeCharacterLinearSum χ s).re - Real.log ‖χ.LFunction s‖| ≤
      primeEulerRemainderConstant := by
  rw [←primeCharacterLog_re χ hs, abs_sub_comm]
  exact (Complex.abs_re_le_norm (primeCharacterLog χ s-primeCharacterLinearSum χ s)).trans
    (primeCharacterLog_linear_error χ hs)

end JointDickman

end OAI
