import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterDirichletSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace OAI

/-! # Analytic factorization of the twisted squarefree Dirichlet series -/
namespace JointDickman

noncomputable def primeCharacterLog {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1-characterPrimePower χ s p)

theorem primeCharacterLog_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1-characterPrimePower χ s p)) := by
  convert! (summable_dirichletSummand χ hs).of_norm.clog_one_sub.neg.subtype Nat.Prime using 1

theorem primeCharacterLog_exp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeCharacterLog χ s) = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact χ.LSeries_eulerProduct_exp_log hs

theorem primeCharacterLog_summand_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖-Complex.log (1-characterPrimePower χ s p)‖ ≤ (3/2:ℝ)*(p.val:ℝ)^(-σ) := by
  have hhalf : ‖characterPrimePower χ s p‖ ≤ 1/2 :=
    (characterPrimePower_norm_le χ p).trans
      (Complex.norm_prime_cpow_le_one_half p (hσ.trans_le hs))
  have hh := Complex.norm_log_one_add_half_le_self
    (z := -characterPrimePower χ s p) (by simpa only [norm_neg] using hhalf)
  rw [norm_neg]
  calc
    _ ≤ (3/2:ℝ)*‖characterPrimePower χ s p‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using hh
    _ ≤ (3/2:ℝ)*‖(p.val:ℂ)^(-s)‖ :=
      mul_le_mul_of_nonneg_left (characterPrimePower_norm_le χ p) (by norm_num)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)

theorem primeCharacterLog_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (primeCharacterLog χ) {s : ℂ | σ < s.re} := by
  have hsum : Summable (fun p : Nat.Primes => (3/2:ℝ)*(p.val:ℝ)^(-σ)) :=
    ((Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype Nat.Prime).mul_left _
  apply Complex.differentiableOn_tsum_of_summable_norm hsum
  · intro p s hs
    have hw : ‖-characterPrimePower χ s p‖ < 1 := by
      rw [norm_neg]
      exact ((characterPrimePower_norm_le χ p).trans
        (Complex.norm_prime_cpow_le_one_half p (by dsimp at hs; linarith))).trans_lt (by norm_num)
    have hc : DifferentiableAt ℂ (fun t => characterPrimePower χ t p) s :=
      (differentiableAt_id.neg.const_cpow (Or.inl
        (by exact_mod_cast p.property.ne_zero))).const_mul _
    exact (((differentiableAt_const (1:ℂ)).sub hc).clog
      (by simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one hw)).neg.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact primeCharacterLog_summand_bound χ hσ hs.le p

theorem primeCharacterLog_analyticOnNhd {q : ℕ} (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (primeCharacterLog χ) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hσ : 1 < (1+s.re)/2 := by dsimp at hs; linarith
  have hm : s ∈ {t : ℂ | (1+s.re)/2 < t.re} := by dsimp at hs ⊢; linarith
  exact (primeCharacterLog_differentiableOn χ hσ).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re) s hm

theorem squarefreeCharacterDirichletSeries_factorization {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s =
      squarefreeCharacterAnalyticFactor χ z s * Complex.exp ((z:ℂ)*primeCharacterLog χ s) := by
  have hG := squarefreeCharacterPrimeLog_summable χ hz hz1 (show 1/2 < s.re by linarith)
  have hZ := (primeCharacterLog_summable χ hs).mul_left (z:ℂ)
  have hsum := (hG.add hZ).hasSum.cexp
  rw [Summable.tsum_add hG hZ, tsum_mul_left, Complex.exp_add] at hsum
  have heq (p : Nat.Primes) :
      Complex.exp (squarefreeCharacterPrimeLog χ z s p+
        (z:ℂ)*(-Complex.log (1-characterPrimePower χ s p))) =
      1+(z:ℂ)*characterPrimePower χ s p := by
    have hn : ‖(z:ℂ)*characterPrimePower χ s p‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt
        (((characterPrimePower_norm_le χ p).trans
          (Complex.norm_prime_cpow_le_one_half p hs)).trans_lt (by norm_num))
    have hne : 1+(z:ℂ)*characterPrimePower χ s p ≠ 0 := by
      intro he
      have hv : (z:ℂ)*characterPrimePower χ s p = -1 := by linear_combination he
      rw [hv, norm_neg, norm_one] at hn
      exact lt_irrefl _ hn
    have hcancel : squarefreeCharacterPrimeLog χ z s p+
        (z:ℂ)*(-Complex.log (1-characterPrimePower χ s p)) =
        Complex.log (1+(z:ℂ)*characterPrimePower χ s p) := by
      unfold squarefreeCharacterPrimeLog squarefreeEulerLog
      ring
    rw [hcancel, Complex.exp_log hne]
  have hp : HasProd (fun p : Nat.Primes => 1+(z:ℂ)*characterPrimePower χ s p)
      (squarefreeCharacterAnalyticFactor χ z s * Complex.exp ((z:ℂ)*primeCharacterLog χ s)) := by
    have hf : (Complex.exp ∘ (fun p : Nat.Primes => squarefreeCharacterPrimeLog χ z s p+
        (z:ℂ)*(-Complex.log (1-characterPrimePower χ s p)))) =
        (fun p => 1+(z:ℂ)*characterPrimePower χ s p) := funext heq
    rw [hf] at hsum
    simpa only [squarefreeCharacterAnalyticFactor, squarefreeCharacterLogFactor,
      primeCharacterLog] using hsum
  exact (squarefreeCharacterDirichletSeries_eulerProduct χ hz hz1 hs).unique hp

end JointDickman

end OAI
