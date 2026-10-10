import OAI.NumberTheory.JointDickman.Analysis.SquarefreeEulerAnalytic
import OAI.NumberTheory.JointDickman.Analysis.CharacterInputs
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace OAI

/-! # The absolutely convergent Euler correction for squarefree character sums -/
namespace JointDickman

noncomputable def characterPrimePower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (p : Nat.Primes) : ℂ := χ (p.val : ZMod q) * (p.val:ℂ)^(-s)

noncomputable def squarefreeCharacterPrimeLog {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  squarefreeEulerLog z (characterPrimePower χ s p)

noncomputable def squarefreeCharacterLogFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) : ℂ := ∑' p : Nat.Primes, squarefreeCharacterPrimeLog χ z s p

noncomputable def squarefreeCharacterAnalyticFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (s : ℂ) : ℂ := Complex.exp (squarefreeCharacterLogFactor χ z s)

theorem characterPrimePower_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (p : Nat.Primes) :
    ‖characterPrimePower χ s p‖ ≤ ‖(p.val:ℂ)^(-s)‖ := by
  rw [characterPrimePower, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem squarefreeCharacterPrimeLog_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 0 < σ)
    {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖squarefreeCharacterPrimeLog χ z s p‖ ≤
      (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ) := by
  have hr : (2:ℝ)^(-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hnorm := (characterPrimePower_norm_le χ p).trans
    (prime_negative_cpow_norm_le hσ.le hs p)
  have hn : ‖characterPrimePower χ s p‖ ≤ (p.val:ℝ)^(-σ) := by
    apply (characterPrimePower_norm_le χ p).trans
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)
  calc
    _ ≤ 2*‖characterPrimePower χ s p‖^2/(1-(2:ℝ)^(-σ)) :=
      squarefreeEulerLog_norm_bound hz hz1 hr hnorm
    _ ≤ 2*((p.val:ℝ)^(-σ))^2/(1-(2:ℝ)^(-σ)) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr hn)
        (by norm_num)
    _ = _ := by
      rw [←Real.rpow_natCast, ←Real.rpow_mul (Nat.cast_nonneg p.val)]
      norm_num only [Nat.cast_ofNat]
      rw [show -σ*(2:ℝ) = -2*σ by ring]
      ring

theorem squarefreeCharacterPrimeLog_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) {s : ℂ} (hs : 1/2 < s.re) :
    Summable (fun p : Nat.Primes => squarefreeCharacterPrimeLog χ z s p) := by
  apply Summable.of_norm
  exact (squarefreePrimeLog_bound_summable hs).of_nonneg_of_le
    (fun p => norm_nonneg _) (fun p => squarefreeCharacterPrimeLog_bound χ hz hz1
      (by linarith) le_rfl p)

theorem squarefreeCharacterPrimeLog_differentiableAt {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    DifferentiableAt ℂ (fun t => squarefreeCharacterPrimeLog χ z t p) s := by
  have hw : ‖characterPrimePower χ s p‖ < 1 :=
    ((characterPrimePower_norm_le χ p).trans (prime_negative_cpow_norm_le hs.le le_rfl p)).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hzw : ‖(z:ℂ)*characterPrimePower χ s p‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz]
    exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt hw
  have hp0 : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hf : DifferentiableAt ℂ (fun t => characterPrimePower χ t p) s :=
    (differentiableAt_id.neg.const_cpow (Or.inl hp0)).const_mul _
  have h₁ := ((differentiableAt_const (1:ℂ)).add
    ((differentiableAt_const (z:ℂ)).mul hf)).clog (Complex.mem_slitPlane_of_norm_lt_one hzw)
  have hslit : 1-characterPrimePower χ s p ∈ Complex.slitPlane := by
    have hh : ‖-characterPrimePower χ s p‖ < 1 := by simpa only [norm_neg] using hw
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh
  exact h₁.add ((differentiableAt_const (z:ℂ)).mul
    (((differentiableAt_const (1:ℂ)).sub hf).clog hslit))

theorem squarefreeCharacterLogFactor_differentiableOn {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 1/2 < σ) :
    DifferentiableOn ℂ (squarefreeCharacterLogFactor χ z) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (squarefreePrimeLog_bound_summable hσ)
  · intro p s hs
    exact (squarefreeCharacterPrimeLog_differentiableAt χ hz hz1
      (by dsimp at hs; linarith) p).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact squarefreeCharacterPrimeLog_bound χ hz hz1 (by linarith) hs.le p

theorem squarefreeCharacterLogFactor_analyticOnNhd {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeCharacterLogFactor χ z) {s : ℂ | 1/2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have hσ : 1/2 < (s.re+1/2)/2 := by dsimp at hs; linarith
  have hmem : s ∈ {t : ℂ | (s.re+1/2)/2 < t.re} := by dsimp at hs ⊢; linarith
  have hopen : IsOpen {t : ℂ | (s.re+1/2)/2 < t.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact ((squarefreeCharacterLogFactor_differentiableOn χ hz hz1 hσ).differentiableAt
    (hopen.mem_nhds hmem)).differentiableWithinAt

theorem squarefreeCharacterAnalyticFactor_analyticOnNhd {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeCharacterAnalyticFactor χ z) {s : ℂ | 1/2 < s.re} :=
  (squarefreeCharacterLogFactor_analyticOnNhd χ hz hz1).cexp

theorem squarefreeCharacterAnalyticFactor_uniform_bound {z σ : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 1/2 < σ) : ∃ C : ℝ, 0 < C ∧
    ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ), σ ≤ s.re →
      ‖squarefreeCharacterAnalyticFactor χ z s‖ ≤ C := by
  let b : Nat.Primes → ℝ := fun p => (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ)
  have hb : Summable b := squarefreePrimeLog_bound_summable hσ
  refine ⟨Real.exp (∑' p, b p),Real.exp_pos _,fun χ s hs => ?_⟩
  have hf := squarefreeCharacterPrimeLog_summable χ hz hz1 (hσ.trans_le hs)
  have hl : ‖squarefreeCharacterLogFactor χ z s‖ ≤ ∑' p, b p := by
    calc
      _ ≤ ∑' p, ‖squarefreeCharacterPrimeLog χ z s p‖ := norm_tsum_le_tsum_norm hf.norm
      _ ≤ _ := hf.norm.tsum_le_tsum
        (fun p => squarefreeCharacterPrimeLog_bound χ hz hz1 (by linarith) hs p) hb
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hl)

end JointDickman

end OAI
