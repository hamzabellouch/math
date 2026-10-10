import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzAnnulusSampling

namespace OAI

/-! # Physical Schwartz dilation and bounded scale ratios

The annulus immediately outside radius L has radius at most 2L.  Its extra
scale ratio lies in [1,2], where finite weighted jets remain uniformly bounded.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartzPhysicalDilation_comp (a R S : ℝ) (hR : 0 < R) (hS : 0 < S)
    (ψ : 𝓢(E, ℂ)) :
    schwartzPhysicalDilation a R hR (schwartzPhysicalDilation a S hS ψ) =
      schwartzPhysicalDilation a (R * S) (mul_pos hR hS) ψ := by
  ext x
  simp only [schwartzPhysicalDilation_apply]
  have harg : S⁻¹ • (R⁻¹ • x) = (R * S)⁻¹ • x := by
    rw [smul_smul, mul_inv_rev]
  rw [harg, Real.mul_rpow hR.le hS.le, Complex.ofReal_mul]
  ring

theorem schwartzPhysicalDilation_jet_norm (a R : ℝ) (hR : 0 < R)
    (ψ : 𝓢(E, ℂ)) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (schwartzPhysicalDilation a R hR ψ) x‖ =
      R ^ (-2 * a) * (R⁻¹) ^ n * ‖iteratedFDeriv ℝ n ψ (R⁻¹ • x)‖ := by
  have hin : ContDiff ℝ ∞ (fun y : E => ψ (R⁻¹ • y)) :=
    ψ.smooth'.comp (contDiff_id.const_smul R⁻¹)
  have hf : (schwartzPhysicalDilation a R hR ψ : E → ℂ) =
      fun y => (R ^ (-2 * a) : ℝ) • ψ (R⁻¹ • y) := by
    funext y
    simp only [schwartzPhysicalDilation_apply, Complex.real_smul]
  have hd : iteratedFDeriv ℝ n (fun y : E => ψ (R⁻¹ • y)) =
      fun y => (R⁻¹) ^ n • iteratedFDeriv ℝ n ψ (R⁻¹ • y) := by
    simpa only using! iteratedFDeriv_comp_const_smul R⁻¹ (ψ.smooth'.of_le (by simp))
  rw [hf, iteratedFDeriv_const_smul_apply' ((hin.of_le (by simp)).contDiffAt), hd]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hR.le _),
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) n)]
  ring

theorem schwartzPhysicalDilation_boundedRatio_jets (a R D : ℝ)
    (ha : 0 < a) (hR : 1 ≤ R) (hR2 : R ≤ 2) (_hD : 0 ≤ D)
    (ψ : 𝓢(E, ℂ)) (N : ℕ)
    (hjet : ∀ n ≤ N, ∀ x : E, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ ≤ D)
    (n : ℕ) (hn : n ≤ N) (x : E) :
    (1 + ‖x‖) ^ N *
      ‖iteratedFDeriv ℝ n (schwartzPhysicalDilation a R (by linarith) ψ) x‖ ≤
        2 ^ N * D := by
  have hRp : 0 < R := by linarith
  have hc : R ^ (-2 * a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hi : (R⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity)
    ((inv_le_one₀ hRp).mpr hR)
  have hderiv : ‖iteratedFDeriv ℝ n (schwartzPhysicalDilation a R hRp ψ) x‖ ≤
      ‖iteratedFDeriv ℝ n ψ (R⁻¹ • x)‖ := by
    rw [schwartzPhysicalDilation_jet_norm]
    have hfac : R ^ (-2 * a) * (R⁻¹) ^ n ≤ 1 := by
      exact (mul_le_mul hc hi (by positivity) (by norm_num)).trans_eq (one_mul _)
    exact mul_le_of_le_one_left (norm_nonneg _) hfac
  have hnorm : ‖x‖ = R * ‖R⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRp),
      ← mul_assoc, mul_inv_cancel₀ hRp.ne', one_mul]
  have hweight : (1 + ‖x‖) ^ N ≤ 2 ^ N * (1 + ‖R⁻¹ • x‖) ^ N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [hnorm]
    nlinarith [norm_nonneg (R⁻¹ • x)]
  calc
    _ ≤ (2 ^ N * (1 + ‖R⁻¹ • x‖) ^ N) * ‖iteratedFDeriv ℝ n ψ (R⁻¹ • x)‖ :=
      mul_le_mul hweight hderiv (norm_nonneg _) (by positivity)
    _ = 2 ^ N * ((1 + ‖R⁻¹ • x‖) ^ N * ‖iteratedFDeriv ℝ n ψ (R⁻¹ • x)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hjet n hn _) (by positivity)

end DefocusingNLS

end OAI
