import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerLog
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeDirichletSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI

/-! # The analytic Euler correction in the half-plane Re(s) > 1/2 -/
namespace JointDickman
open scoped Topology

noncomputable def squarefreePrimeLog (z : ℝ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  squarefreeEulerLog z ((p.val:ℂ)^(-s))

noncomputable def squarefreeLogFactor (z : ℝ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, squarefreePrimeLog z s p

noncomputable def squarefreeAnalyticFactor (z : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (squarefreeLogFactor z s)

 theorem prime_negative_cpow_norm_le {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re)
    (p : Nat.Primes) : ‖(p.val:ℂ)^(-s)‖ ≤ (2:ℝ)^(-σ) := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re]
  calc
    _ ≤ (p.val:ℝ)^(-σ) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast p.property.one_le) (by linarith)
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast p.property.two_le) (by linarith)

 theorem squarefreePrimeLog_uniform_bound {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖squarefreePrimeLog z s p‖ ≤ (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ) := by
  have hr : (2:ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hn : ‖(p.val:ℂ)^(-s)‖ ≤ (p.val:ℝ)^(-σ) := by
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)
  calc
    _ ≤ 2*‖(p.val:ℂ)^(-s)‖^2/(1-(2:ℝ)^(-σ)) :=
      squarefreeEulerLog_norm_bound hz hz1 hr (prime_negative_cpow_norm_le hσ.le hs p)
    _ ≤ 2*((p.val:ℝ)^(-σ))^2/(1-(2:ℝ)^(-σ)) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr hn) (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg p.val)]
      norm_num only [Nat.cast_ofNat]
      rw [show -σ*(2:ℝ) = -2*σ by ring]
      ring

 theorem squarefreePrimeLog_bound_summable {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun p : Nat.Primes => (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ)) := by
  have hsum : Summable (fun n : ℕ => (n:ℝ)^(-2*σ)) := Real.summable_nat_rpow.mpr (by linarith)
  exact (hsum.subtype Nat.Prime).mul_left _

 theorem squarefreePrimeLog_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1/2 < s.re) : Summable (fun p : Nat.Primes => squarefreePrimeLog z s p) := by
  apply Summable.of_norm
  exact (squarefreePrimeLog_bound_summable hs).of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => squarefreePrimeLog_uniform_bound hz hz1 (by linarith) le_rfl p)

 theorem squarefreePrimeLog_differentiableAt {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    DifferentiableAt ℂ (fun t => squarefreePrimeLog z t p) s := by
  have hw : ‖(p.val:ℂ)^(-s)‖ < 1 :=
    (prime_negative_cpow_norm_le hs.le le_rfl p).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hzw : ‖(z:ℂ)*(p.val:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
    exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt hw
  have hp0 : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hf : DifferentiableAt ℂ (fun t : ℂ => (p.val:ℂ)^(-t)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hp0)
  have h₁ := ((differentiableAt_const (1:ℂ)).add ((differentiableAt_const (z:ℂ)).mul hf)).clog
    (Complex.mem_slitPlane_of_norm_lt_one hzw)
  have hslit : 1-(p.val:ℂ)^(-s) ∈ Complex.slitPlane := by
    have hh : ‖-((p.val:ℂ)^(-s))‖ < 1 := by simpa only [norm_neg] using hw
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh
  have h₂ := ((differentiableAt_const (1:ℂ)).sub hf).clog hslit
  exact h₁.add ((differentiableAt_const (z:ℂ)).mul h₂)

 theorem squarefreeLogFactor_differentiableOn {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 1/2 < σ) : DifferentiableOn ℂ (squarefreeLogFactor z) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (squarefreePrimeLog_bound_summable hσ)
  · intro p s hs
    exact (squarefreePrimeLog_differentiableAt hz hz1 (by dsimp at hs; linarith) p).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact squarefreePrimeLog_uniform_bound hz hz1 (by linarith) hs.le p

 theorem squarefreeLogFactor_analyticOnNhd {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeLogFactor z) {s : ℂ | 1/2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have hσ : 1/2 < (s.re+1/2)/2 := by dsimp at hs; linarith
  have hmem : s ∈ {t : ℂ | (s.re+1/2)/2 < t.re} := by dsimp at hs ⊢; linarith
  have hopen : IsOpen {t : ℂ | (s.re+1/2)/2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  exact ((squarefreeLogFactor_differentiableOn hz hz1 hσ).differentiableAt (hopen.mem_nhds hmem)).differentiableWithinAt

 theorem squarefreeAnalyticFactor_analyticOnNhd {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeAnalyticFactor z) {s : ℂ | 1/2 < s.re} :=
  (squarefreeLogFactor_analyticOnNhd hz hz1).cexp

 theorem squarefreeAnalyticFactor_ne_zero (z : ℝ) (s : ℂ) : squarefreeAnalyticFactor z s ≠ 0 :=
  Complex.exp_ne_zero _

end JointDickman

end OAI
