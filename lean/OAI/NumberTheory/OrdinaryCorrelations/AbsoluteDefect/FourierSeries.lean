import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogBin

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory

namespace OrdinaryDirichletMeanSquare
open Filter

def fourierSeries (a : ℕ → ℂ) (u : ℕ → ℝ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, a n * phase (u n) x

lemma fourier_summable {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖))
    (u : ℕ → ℝ) (x : ℝ) : Summable (fun n => a n*phase (u n) x) := by
  apply Summable.of_norm
  simpa only [norm_mul,norm_phase,mul_one] using ha

lemma continuous_fourierSeries {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖))
    (u : ℕ → ℝ) : Continuous (fourierSeries a u) := by
  apply continuous_tsum (fun n => by unfold phase; fun_prop) ha
  intro n x
  simp only [norm_mul,norm_phase,mul_one,le_rfl]

lemma gaussian_series_integrable {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖))
    (u : ℕ → ℝ) :
    Integrable (fun x : ℝ => gaussian x*‖fourierSeries a u x‖^2) := by
  have hc : Continuous (fun x : ℝ => gaussian x*‖fourierSeries a u x‖^2) := by
    have hf := continuous_fourierSeries ha u
    unfold gaussian
    fun_prop
  apply Integrable.mono' (gaussian_integrable.mul_const ((∑' n, ‖a n‖)^2))
    hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussian_nonneg _) (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (gaussian_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  have h := norm_tsum_le_tsum_norm (fourier_summable ha u x).norm
  simpa only [fourierSeries,norm_mul,norm_phase,mul_one] using h

theorem gaussian_series_energy {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖))
    (u : ℕ → ℝ) {C : ℝ}
    (hC : ∀ N : ℕ, (∫ x : ℝ, gaussian x *
      ‖polynomial (Finset.range N) a u x‖^2) ≤ C) :
    (∫ x : ℝ, gaussian x*‖fourierSeries a u x‖^2) ≤ C := by
  have ht : Tendsto (fun N : ℕ => ∫ x : ℝ, gaussian x*
      ‖polynomial (Finset.range N) a u x‖^2) atTop
      (nhds (∫ x : ℝ, gaussian x*‖fourierSeries a u x‖^2)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => gaussian x*(∑' n, ‖a n‖)^2)
    · intro N
      exact (gaussian_polynomial_integrable _ _ _).aestronglyMeasurable
    · exact gaussian_integrable.mul_const _
    · intro N
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussian_nonneg _) (sq_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (gaussian_nonneg _)
      apply pow_le_pow_left₀ (norm_nonneg _)
      calc
        _ ≤ ∑ n ∈ Finset.range N, ‖a n‖ := by
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro n hn
          simp only [norm_mul,norm_phase,mul_one,le_rfl]
        _ ≤ ∑' n, ‖a n‖ := ha.sum_le_tsum _ (fun n _ => norm_nonneg _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((fourier_summable ha u x).hasSum.tendsto_sum_nat).norm.pow 2)
  exact le_of_tendsto ht (Filter.Eventually.of_forall hC)

lemma mangoldt_coefficient_summable (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {δ : ℝ} (hδ : 0<δ) : Summable (fun n => ‖mangoldtCoefficient f δ n‖) := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s:=((1+δ:ℝ):ℂ)) (by simpa using (lt_add_of_pos_right (1:ℝ) hδ))).norm
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply (mangoldt_coefficient_bound f hf δ n).trans
  rw [LSeries.norm_term_eq]
  by_cases hn : n=0
  · simp [hn]
  · rw [ite_eq_right hn,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_def_of_pos (show (0:ℝ)<n by exact_mod_cast Nat.pos_of_ne_zero hn),
      div_eq_mul_inv,←Real.exp_neg]
    have he : -(1+δ)*Real.log n = -(Real.log n*(1+δ)) := by ring
    rw [he]

lemma mangoldt_polynomial_erase_zero (s : Finset ℕ) (f : ℕ → ℂ)
    (δ x : ℝ) :
    polynomial (s.erase 0) (mangoldtCoefficient f δ) (fun n => Real.log n) x =
      polynomial s (mangoldtCoefficient f δ) (fun n => Real.log n) x := by
  apply Finset.sum_subset (Finset.erase_subset 0 s)
  intro n hn hne
  have hn0 : n=0 := by simpa only [Finset.mem_erase,hn,and_true,not_not] using hne
  simp [hn0,mangoldtCoefficient]

theorem mangoldt_series_gaussian_energy (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {δ : ℝ} (hδ : 0<δ) :
    (∫ x : ℝ, gaussian x *
      ‖fourierSeries (mangoldtCoefficient f δ) (fun n => Real.log n) x‖^2) ≤
      gaussianConstant * Real.exp 3 * 4 *
        (chebyshevConstant * Real.exp 1)^2 * (2+1/δ) := by
  apply gaussian_series_energy (mangoldt_coefficient_summable f hf hδ)
  intro N
  have h := mangoldt_gaussian_energy ((Finset.range N).erase 0)
    (fun n hn => Nat.pos_of_ne_zero (Finset.mem_erase.mp hn).1) f hf hδ
  simpa only [mangoldt_polynomial_erase_zero] using h

end OrdinaryDirichletMeanSquare

end

end OAI
