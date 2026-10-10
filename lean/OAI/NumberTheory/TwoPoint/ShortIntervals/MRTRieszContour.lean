import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszPole

namespace OAI

/-! The finite residue shift for the actual smoothed Mangoldt integrand.
Analytic input appears only as nonvanishing and boundary norm bounds. -/

namespace TwoPointCorrelations

open Complex Set MeasureTheory _root_.Erdos970 _root_.OAI.Erdos970
open scoped Topology

lemma mrt_zeta_riesz_residue {x a b T u : ℝ} (hx : 0 < x)
    (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hb : 1 < b) (hu : |u| < T)
    (hzero : ∀ s ∈ Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
      s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0) :
    RectangleIntegral' (mrtZetaRieszIntegrand x u)
      ((a : ℂ) - Complex.I * (T : ℂ)) ((b : ℂ) + Complex.I * (T : ℂ)) =
        mrtRieszKernel x (1 - (u : ℂ) * Complex.I) := by
  have hab : a ≤ b := by linarith
  have hT : 0 < T := (abs_nonneg u).trans_lt hu
  apply ResidueTheoremOnRectangleWithSimplePole' (p := 1 - (u : ℂ) * Complex.I)
  · simpa using hab
  · simp
    linarith
  · rw [rectangle_mem_nhds_iff]
    simpa [Complex.mem_reProdIm, uIoo_of_le hab, uIoo_of_le (show -T ≤ T by linarith),
      Complex.mul_re, Complex.mul_im] using
      (show (a < 1 ∧ 1 < b) ∧ -T < -u ∧ -u < T from ⟨⟨ha1, hb⟩, by
        have := abs_lt.mp hu
        linarith, by have := abs_lt.mp hu; linarith⟩)
  · intro s hs
    have hsr : a ≤ s.re := by
      have hh : s.re ∈ Icc a b ∧ s.im ∈ Icc (-T) T := by
        simpa [Rectangle, Complex.mem_reProdIm, uIcc_of_le hab,
          uIcc_of_le (show -T ≤ T by linarith)] using hs.1
      exact hh.1.1
    have hne : s + (u : ℂ) * Complex.I ≠ 1 := by
      intro he
      apply hs.2
      change s = 1 - (u : ℂ) * Complex.I
      linear_combination he
    have hn := hzero s hs.1 hne
    have hadd : DifferentiableAt ℂ (fun z : ℂ => z + (u : ℂ) * Complex.I) s := by fun_prop
    have hd := ((analyticOn_riemannZeta _ hne).deriv.differentiableAt.comp s hadd).neg
    have hz := (differentiableAt_riemannZeta hne).comp s hadd
    have hk := mrt_riesz_kernel_differentiableAt hx (s := s)
      (by intro he; have hh := congrArg Complex.re he; simp at hh; linarith)
      (by intro he; have hh := congrArg Complex.re he; simp at hh; linarith)
      (by intro he; have hh := congrArg Complex.re he; norm_num at hh; linarith)
    exact ((hd.div hz hn).mul hk).differentiableWithinAt
  · exact mrt_riesz_integrand_simple_pole hx u

theorem mrt_zeta_riesz_finite_shift {x a b T u B : ℝ}
    (hx : 1 ≤ x) (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hb : 1 < b)
    (hu : |u| < T) (hB : 0 ≤ B)
    (hzero : ∀ s ∈ Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
        ((b : ℂ) + Complex.I * (T : ℂ)),
      s + (u : ℂ) * Complex.I ≠ 1 → riemannZeta (s + (u : ℂ) * Complex.I) ≠ 0)
    (hleft : ∀ t ∈ Icc (-T) T,
      ‖-deriv riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B)
    (hside : ∀ σ ∈ Icc a b, ∀ t : ℝ, |t| = T →
      ‖-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I + (u : ℂ) * Complex.I)‖ ≤ B) :
    ‖(1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      VIntegral (mrtZetaRieszIntegrand x u) b (-T) T‖ ≤
        4 * x / (1 + u ^ 2) +
          (4 * B * x ^ a * Real.pi + 4 * B * x ^ b / T ^ 3 * (b - a)) / (2 * Real.pi) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hT : 0 < T := (abs_nonneg u).trans_lt hu
  have hab : a ≤ b := by linarith
  have hres := mrt_zeta_riesz_residue hx0 ha ha1 hb hu hzero
  have hsides (t : ℝ) (ht : |t| = T) : ∀ σ ∈ Icc a b,
      ‖mrtZetaRieszIntegrand x u ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        2 * B * x ^ b / T ^ 3 := by
    intro σ hσ
    have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
    rw [mrtZetaRieszIntegrand, norm_mul]
    have hh := mul_le_mul (hside σ hσ t ht) (mrt_riesz_kernel_cubic hx0 σ ht0)
      (norm_nonneg _) hB
    rw [ht] at hh
    apply hh.trans
    have hp := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * B by positivity)
    calc
      B * (2 * x ^ σ / T ^ 3) = (2 * B * x ^ σ) / T ^ 3 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hm (by positivity)
  have hv : ‖VIntegral (mrtZetaRieszIntegrand x u) a (-T) T‖ ≤
      4 * B * x ^ a * Real.pi := by
    apply modFive_vertical_quadratic_bound hT.le (by positivity)
    intro t ht
    rw [mrtZetaRieszIntegrand, norm_mul]
    exact (mul_le_mul (hleft t ht) (mrt_riesz_kernel_vertical hx0 ha t)
      (norm_nonneg _) hB).trans_eq (by ring)
  have hh := mrt_rectangle_pole_shift_bound hab hres
    (hsides T (abs_of_pos hT)) (hsides (-T) (by simp [abs_of_pos hT]))
  have hadd := norm_add_le
    ((1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      VIntegral (mrtZetaRieszIntegrand x u) b (-T) T - mrtRieszKernel x (1 - (u : ℂ) * Complex.I))
    (mrtRieszKernel x (1 - (u : ℂ) * Complex.I))
  rw [sub_add_cancel] at hadd
  apply hadd.trans
  have hp := mrt_riesz_kernel_pole hx0 u
  have hsum : ‖VIntegral (mrtZetaRieszIntegrand x u) a (-T) T‖ +
      2 * (2 * B * x ^ b / T ^ 3) * (b - a) ≤
      4 * B * x ^ a * Real.pi + 2 * (2 * B * x ^ b / T ^ 3) * (b - a) := by
    linarith only [hv]
  have hv' := div_le_div_of_nonneg_right hsum (show 0 ≤ 2 * Real.pi by positivity)
  exact (add_le_add (hh.trans hv') hp).trans_eq (by ring)

end TwoPointCorrelations

end OAI
