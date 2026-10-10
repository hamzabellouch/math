import OAI.Combinatorics.EditApproximation.Probability.BernsteinEnvelope

namespace OAI

namespace EditApproximation
open MeasureTheory ProbabilityTheory
open scoped BigOperators

section MGF
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounded_square_integrable (X : Ω → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hm : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω => (X ω) ^ 2) μ := by
  apply Integrable.of_mem_Icc 0 (b ^ 2) (hm.pow_const 2).aemeasurable
  filter_upwards [hbound] with ω hω
  refine ⟨sq_nonneg _, ?_⟩
  have h := mul_le_mul hω hω (abs_nonneg _) hb
  simpa only [← pow_two, sq_abs] using h

theorem bounded_centered_mgf (X : Ω → ℝ) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
    (htb : t * b < 3) (hm : Measurable X) (hi : Integrable X μ)
    (hmean : (∫ ω, X ω ∂μ) = 0) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    mgf X μ t ≤ Real.exp ((t ^ 2 / (2 * (1 - t * b / 3))) * ∫ ω, (X ω) ^ 2 ∂μ) := by
  let c := t ^ 2 / (2 * (1 - t * b / 3))
  have hd : 0 < 2 * (1 - t * b / 3) := by linarith
  have hi2 := bounded_square_integrable μ X b hb.le hm hbound
  have hexp := integrable_exp_mul_of_le t b ht hm.aemeasurable
    (hbound.mono fun ω hω => (le_abs_self _).trans hω)
  have hpoint : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 + t * X ω + c * (X ω) ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hu : t * X ω ≤ t * b := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hω) ht
    have hx := exp_le_bernstein_envelope (t * X ω) (hu.trans_lt htb)
    have hdiv : (t * X ω) ^ 2 / (2 * (1 - t * X ω / 3)) ≤
        (t * X ω) ^ 2 / (2 * (1 - t * b / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) hd
      linarith
    calc
      _ ≤ 1 + t * X ω + (t * X ω) ^ 2 / (2 * (1 - t * X ω / 3)) := hx
      _ ≤ 1 + t * X ω + (t * X ω) ^ 2 / (2 * (1 - t * b / 3)) := add_le_add le_rfl hdiv
      _ = _ := by dsimp only [c]; ring
  have h1 : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have hit := hi.const_mul t
  have hic := hi2.const_mul c
  have hineq := integral_mono_ae hexp ((h1.add hit).add hic) hpoint
  simp only [Pi.add_apply] at hineq
  have hadd := integral_add (h1.add hit) hic
  have hadd' := integral_add h1 hit
  simp only [Pi.add_apply] at hadd hadd'
  rw [hadd, hadd', integral_const_mul, integral_const_mul, hmean] at hineq
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero] at hineq
  exact hineq.trans (by simpa only [add_comm] using Real.add_one_le_exp (c * ∫ ω, (X ω) ^ 2 ∂μ))

theorem bounded_centered_sum_mgf {n : ℕ} (X : Fin n → Ω → ℝ)
    (b v t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) (htb : t * b < 3)
    (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ v) :
    mgf (fun ω => ∑ i, X i ω) μ t ≤ Real.exp (t ^ 2 * v / (2 * (1 - t * b / 3))) := by
  have hmgf := hind.mgf_sum hm Finset.univ (t := t)
  have hsum : (∑ i, X i) = fun ω => ∑ i, X i ω := by
    ext ω
    simp only [Finset.sum_apply]
  rw [hsum] at hmgf
  rw [hmgf]
  let c := t ^ 2 / (2 * (1 - t * b / 3))
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) (by linarith)
  calc
    _ ≤ ∏ i, Real.exp (c * ∫ ω, (X i ω) ^ 2 ∂μ) :=
      Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ =>
        bounded_centered_mgf μ (X i) b t hb ht htb (hm i) (hi i) (hmean i) (hbound i))
    _ = Real.exp (c * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) := by
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (c * v) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvar hc)
    _ = _ := by congr 1; dsimp only [c]; ring

end MGF
end EditApproximation

end OAI
