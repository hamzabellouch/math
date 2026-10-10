import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszKernel

namespace OAI

/-! Absolute series interchange and the exact finite quadratic Riesz
formula for arbitrary absolutely convergent Dirichlet series. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Erdos970
open scoped BigOperators

lemma mrt_riesz_term_kernel (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    LSeries.term a s n * mrtRieszKernel x s =
      a n * mrtRieszKernel (x / (n : ℝ)) s := by
  rw [LSeries.term_of_ne_zero hn]
  unfold mrtRieszKernel
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
  push_cast
  ring

lemma mrt_riesz_term_integrable (a : ℕ → ℂ) (n : ℕ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [mrt_riesz_term_kernel a hn hx]
    exact (mrt_riesz_kernel_integrable (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      hσ).const_mul (a n)

lemma mrt_riesz_term_norm (a : ℕ → ℂ) (n : ℕ) (x σ t : ℝ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖LSeries.term a (σ : ℂ) n‖ *
        ‖mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rw [norm_mul]
  congr 1
  simp [LSeries.norm_term_eq]

theorem mrt_riesz_series_interchange (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * mrtRieszKernel x s) σ =
      ∑' n : ℕ, VerticalIntegral'
        (fun s => LSeries.term a s n * mrtRieszKernel x s) σ := by
  have hi := mrt_riesz_kernel_integrable hx hσ
  have hterms := fun n => mrt_riesz_term_integrable a n hx hσ
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        mrtRieszKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    simp_rw [mrt_riesz_term_norm, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm hterms hnorm
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => tsum_mul_right.symm

lemma mrt_riesz_term_value (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    VerticalIntegral' (fun s => LSeries.term a s n * mrtRieszKernel x s) σ =
      a n * mrtRieszSquare ((n : ℝ) / x) := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk : (fun s => LSeries.term a s n * mrtRieszKernel x s) =
      fun s => a n * mrtRieszKernel (x / (n : ℝ)) s := by
    funext s
    exact mrt_riesz_term_kernel a hn hx s
  rw [hk]
  have hconst : VerticalIntegral' (fun s => a n * mrtRieszKernel (x / (n : ℝ)) s) σ =
      a n * VerticalIntegral' (mrtRieszKernel (x / (n : ℝ))) σ := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, integral_const_mul]
    ring
  rw [hconst, mrt_riesz_inversion (div_pos hx hn') hσ]
  congr 2
  field_simp

theorem mrt_riesz_finite_sum (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * mrtRieszKernel x s) σ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * mrtRieszSquare ((n : ℝ) / x) := by
  rw [mrt_riesz_series_interchange a hx hσ ha]
  have hz : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊,
      VerticalIntegral' (fun s => LSeries.term a s n * mrtRieszKernel x s) σ = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [VerticalIntegral', VerticalIntegral]
    · rw [mrt_riesz_term_value a hn0 hx hσ]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hlarge : ⌊x⌋₊ < n := by
        by_contra! h
        exact hn (Finset.mem_Icc.mpr ⟨hn1, h⟩)
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hlarge
      have hquot : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (by linarith)
      simp [mrtRieszSquare, max_eq_right (by linarith : 1 - (n : ℝ) / x ≤ 0)]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro n hn
  exact mrt_riesz_term_value a (by have hh := (Finset.mem_Icc.mp hn).1; omega) hx hσ

end TwoPointCorrelations

end OAI
