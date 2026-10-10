import OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronInversion

namespace OAI

/-! Absolute interchange for the triangular Perron kernel. The estimate is
proved for any absolutely convergent Dirichlet series and then specialized
to the actual twisted von Mangoldt series.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory Erdos970
open scoped BigOperators

lemma modFivePerron_term_kernel (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    LSeries.term a s n * modFivePerronKernel x s =
      a n * modFivePerronKernel (x / (n : ℝ)) s := by
  rw [LSeries.term_of_ne_zero hn]
  unfold modFivePerronKernel
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
  push_cast
  ring

lemma modFivePerron_term_integrable (a : ℕ → ℂ) (n : ℕ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [modFivePerron_term_kernel a hn hx]
    exact (modFivePerronKernel_integrable (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      hσ).const_mul (a n)

lemma modFivePerron_term_norm (a : ℕ → ℂ) (n : ℕ) (x σ t : ℝ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖LSeries.term a (σ : ℂ) n‖ *
        ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rw [norm_mul]
  congr 1
  simp [LSeries.norm_term_eq]

theorem modFivePerron_series_interchange (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑' n : ℕ, VerticalIntegral'
        (fun s => LSeries.term a s n * modFivePerronKernel x s) σ := by
  have hi := modFivePerronKernel_integrable hx hσ
  have hterms := fun n => modFivePerron_term_integrable a n hx hσ
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    simp_rw [modFivePerron_term_norm, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm hterms hnorm
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => tsum_mul_right.symm

lemma modFivePerron_term_value (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (hxn : x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ =
      if (n : ℝ) < x then a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk : (fun s => LSeries.term a s n * modFivePerronKernel x s) =
      fun s => a n * modFivePerronKernel (x / (n : ℝ)) s := by
    funext s
    exact modFivePerron_term_kernel a hn hx s
  rw [hk]
  have hconst : VerticalIntegral' (fun s => a n * modFivePerronKernel (x / (n : ℝ)) s) σ =
      a n * VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, integral_const_mul]
    ring
  rw [hconst]
  by_cases hnlt : (n : ℝ) < x
  · rw [ite_eq_left hnlt]
    have hp := modFivePerron_gt_one ((one_lt_div hn').mpr hnlt) hσ
    change VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = _ at hp
    rw [hp]
    congr 1
    push_cast
    field_simp
  · rw [ite_eq_right hnlt]
    have hlt : x < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt hnlt) hxn
    have hp := modFivePerron_lt_one (div_pos hx hn') ((div_lt_one hn').mpr hlt) hσ
    change VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = 0 at hp
    rw [hp, mul_zero]

end TwoPointCorrelations

end OAI
