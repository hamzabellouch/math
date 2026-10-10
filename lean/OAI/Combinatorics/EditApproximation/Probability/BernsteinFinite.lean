import OAI.Combinatorics.EditApproximation.Probability.BernsteinMGF

namespace OAI

/-! Finite scalar Bernstein concentration for independent
centered bounded real sums with a summed second-moment upper bound. -/

namespace EditApproximation
open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem bernstein_chernoff_exponent (b v d : ℝ) (hb : 0 < b)
    (hv : 0 < v) (hd : 0 < d) :
    let t := d / (v + b * d / 3);
    -t * d + t ^ 2 * v / (2 * (1 - t * b / 3)) =
      -d ^ 2 / (2 * v + (2 / 3 : ℝ) * b * d) := by
  let D := v + b * d / 3
  have hD : D ≠ 0 := ne_of_gt (by dsimp only [D]; positivity)
  have hunit : 1 - (d / D) * b / 3 = v / D := by
    field_simp [hD]
    dsimp only [D]
    ring
  change -(d / D) * d + (d / D) ^ 2 * v / (2 * (1 - (d / D) * b / 3)) = _
  rw [hunit]
  have hfinal : 2 * v + (2 / 3 : ℝ) * b * d = 2 * D := by dsimp only [D]; ring
  rw [hfinal]
  field_simp [hD, hv.ne']
  ring

theorem finite_bernstein_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (b v d : ℝ)
    (hb : 0 < b) (hv : 0 < v) (hd : 0 < d)
    (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ v) :
    μ.real {ω | d ≤ ∑ i, X i ω} ≤
      Real.exp (-d ^ 2 / (2 * v + (2 / 3 : ℝ) * b * d)) := by
  let t := d / (v + b * d / 3)
  have hden : 0 < v + b * d / 3 := by positivity
  have ht : 0 ≤ t := (div_pos hd hden).le
  have htb : t * b < 3 := by
    dsimp only [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith only [hv]
  have heach (i : Fin n) : Integrable (fun ω => Real.exp (t * X i ω)) μ :=
    integrable_exp_mul_of_le t b ht (hm i).aemeasurable
      ((hbound i).mono fun ω hω => (le_abs_self _).trans hω)
  have hsum : (∑ i, X i) = fun ω => ∑ i, X i ω := by
    ext ω
    simp only [Finset.sum_apply]
  have hsumint := hind.integrable_exp_mul_sum hm (s := Finset.univ) (fun i _ => heach i)
  rw [hsum] at hsumint
  have htail := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω) d ht hsumint
  have hmgf := bounded_centered_sum_mgf μ X b v t hb ht htb hind hm hi hmean hbound hvar
  calc
    _ ≤ Real.exp (-t * d) * mgf (fun ω => ∑ i, X i ω) μ t := htail
    _ ≤ Real.exp (-t * d) * Real.exp (t ^ 2 * v / (2 * (1 - t * b / 3))) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      exact bernstein_chernoff_exponent b v d hb hv hd

/-- Two-sided Bernstein concentration for independent centered bounded sums. -/
theorem finiteBernsteinInput {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : FiniteBernsteinInput μ := by
  intro n X b v d hb hv hd hind hm hi hmean hbound hvar
  have hplus := finite_bernstein_upper μ X b v d hb hv hd hind hm hi hmean hbound hvar
  have hnegind : iIndepFun (fun i ω => -X i ω) μ :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hnegmean (i) : (∫ ω, -X i ω ∂μ) = 0 := by rw [integral_neg, hmean, neg_zero]
  have hnegvar : (∑ i, ∫ ω, (-X i ω) ^ 2 ∂μ) ≤ v := by simpa only [neg_sq] using hvar
  have hminus := finite_bernstein_upper μ (fun i ω => -X i ω) b v d hb hv hd hnegind
    (fun i => (hm i).neg) (fun i => (hi i).neg) hnegmean
    (fun i => (hbound i).mono fun ω hω => by simpa only [abs_neg] using hω) hnegvar
  have hevent : {ω | d ≤ |∑ i, X i ω|} =
      {ω | d ≤ ∑ i, X i ω} ∪ {ω | d ≤ ∑ i, -X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.sum_neg_distrib]
    rw [le_abs]
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith only [hplus, hminus])

end EditApproximation

end OAI
