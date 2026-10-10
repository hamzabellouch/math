import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowUniformGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreTail

namespace OAI

/-! # A common integrable bound for parameter-dependent Laguerre coefficients -/

open MeasureTheory Set Polynomial

namespace DefocusingNLS

theorem exists_slowLaguerre_parameter_majorant (q : ℂ) (m n : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi 0) ∧
      ∀ z ∈ Metric.closedBall q (2 * ρ), -1 < z.re ∧
        ∀ t : ℝ, 0 < t →
          ‖laguerreIntegrand (shiftedSlowDerivative 0 z m s) n t‖ ≤ bound t := by
  let ρ : ℝ := (q.re + 1) / 4
  let a : ℝ := q.re - 2 * ρ
  let b : ℝ := q.re + 2 * ρ
  let M : ℝ := ‖(m : ℂ) - 1 - q‖ + 2 * ρ
  let A : ℝ := ‖q‖ + 2 * ρ
  let δ : ℝ := |s.im|
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have ha : -1 < a := by dsimp [a, ρ]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hδ : 0 < δ := abs_pos.mpr hsim
  have hparams (z : ℂ) (hz : z ∈ Metric.closedBall q (2 * ρ)) :
      a ≤ z.re ∧ z.re ≤ b ∧ ‖(m : ℂ) - 1 - z‖ ≤ M ∧ ‖z‖ ≤ A := by
    have hn : ‖z - q‖ ≤ 2 * ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hu := (Complex.re_le_norm (z - q)).trans hn
    have hl : (q - z).re ≤ 2 * ρ := by
      apply (Complex.re_le_norm (q - z)).trans
      simpa only [norm_sub_rev] using hn
    have hr : ‖(m : ℂ) - 1 - z‖ ≤ ‖(m : ℂ) - 1 - q‖ + ‖z - q‖ := by
      calc
        _ = ‖((m : ℂ) - 1 - q) - (z - q)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hnq : ‖z‖ ≤ ‖q‖ + ‖z - q‖ := by
      calc
        _ = ‖q + (z - q)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    simp only [Complex.sub_re] at hu hl
    exact ⟨by dsimp [a]; linarith, by dsimp [b]; linarith,
      by dsimp [M]; linarith, by dsimp [A]; linarith⟩
  have hγcont : Continuous (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  obtain ⟨G, hG⟩ := (isCompact_closedBall q (2 * ρ)).exists_bound_of_continuousOn hγcont.continuousOn
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG q (Metric.mem_closedBall_self (by positivity)))
  obtain ⟨C, hC, hb⟩ := exists_regularizedSlowSolution_uniform_bound m a b M δ A G
    ha hab hM hδ hA hG0
  obtain ⟨N, hN⟩ := exists_nat_gt A
  let P : ℂ[X] := (1 + X) ^ N * laguerrePolynomial n
  let D : ℝ := C * (1 + ‖s‖) ^ A
  refine ⟨ρ, hρ, fun t => D * ‖(Real.exp (-t) : ℂ) * P.eval (t : ℂ)‖,
    (integrableOn_exp_neg_polynomial P).norm.const_mul D, ?_⟩
  intro z hz
  obtain ⟨hza, hzb, hzm, hzA⟩ := hparams z hz
  refine ⟨ha.trans_le hza, ?_⟩
  intro t ht
  have hxδ : δ ≤ ‖(t : ℂ) - s‖ := by
    simpa only [δ, Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((t : ℂ) - s)
  have hxre : 0 ≤ ((t : ℂ) - s).re := by simp [hsre, ht.le]
  have hxn : 1 + ‖(t : ℂ) - s‖ ≤ (1 + ‖s‖) * (1 + t) := by
    have h := norm_sub_le (t : ℂ) s
    rw [Complex.norm_of_nonneg ht.le] at h
    nlinarith [norm_nonneg s]
  have hbound : ‖regularizedSlowSolution z m ((t : ℂ) - s)‖ ≤ D * (1 + t) ^ N := by
    calc
      _ ≤ C * (1 + ‖(t : ℂ) - s‖) ^ A := hb z _ hza hzb hzm hzA (hG z hz) hxre hxδ
      _ ≤ C * ((1 + ‖s‖) * (1 + t)) ^ A := by gcongr
      _ = D * (1 + t) ^ A := by rw [Real.mul_rpow (by positivity) (by positivity)]; dsimp [D]; ring
      _ ≤ D * (1 + t) ^ N := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [D]; positivity)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) hN.le
  have hnorm : ‖(1 : ℂ) + (t : ℂ)‖ = 1 + t := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_of_nonneg (by linarith)]
  simp only [laguerreIntegrand, shiftedSlowDerivative, iteratedDeriv_zero, laguerreValue,
    P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X, norm_mul, norm_pow, hnorm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * ‖regularizedSlowSolution z m ((t : ℂ) - s)‖ *
        ‖(laguerrePolynomial n).eval (t : ℂ)‖ ≤
      Real.exp (-t) * (D * (1 + t) ^ N) * ‖(laguerrePolynomial n).eval (t : ℂ)‖ := by gcongr
    _ = _ := by ring

end DefocusingNLS

end OAI
