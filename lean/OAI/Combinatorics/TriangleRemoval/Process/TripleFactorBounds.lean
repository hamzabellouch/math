import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction
open scoped BigOperators

namespace SharpTerminalLeave

theorem triple_factor_bounds {a b c ε : ℝ}
    (hε : ε ≤ 1 / 2) (ha : a ∈ Set.Icc 0 ε)
    (hb : b ∈ Set.Icc 0 ε) (hc : c ∈ Set.Icc 0 ε) :
    1 / 8 ≤ (1 - a) * (1 - b) * (1 - c) ∧
    (1 - a) * (1 - b) * (1 - c) ≤ 1 ∧
    |1 - (1 - a) * (1 - b) * (1 - c)| ≤ 3 * ε := by
  have ha' : 1 / 2 ≤ 1 - a := by linarith [ha.2]
  have hb' : 1 / 2 ≤ 1 - b := by linarith [hb.2]
  have hc' : 1 / 2 ≤ 1 - c := by linarith [hc.2]
  have hab : 1 / 4 ≤ (1 - a) * (1 - b) := by
    nlinarith [mul_le_mul ha' hb' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : 0 ≤ 1 - a)]
  have hl : 1 / 8 ≤ (1 - a) * (1 - b) * (1 - c) := by
    nlinarith [mul_le_mul hab hc' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : 0 ≤ (1 - a) * (1 - b))]
  have hab1 : (1 - a) * (1 - b) ≤ 1 := by
    nlinarith [mul_le_mul (by linarith [ha.1] : 1 - a ≤ 1)
      (by linarith [hb.1] : 1 - b ≤ 1) (by linarith : 0 ≤ 1 - b) zero_le_one]
  have hu : (1 - a) * (1 - b) * (1 - c) ≤ 1 := by
    nlinarith [mul_le_mul hab1 (by linarith [hc.1] : 1 - c ≤ 1)
      (by linarith : 0 ≤ 1 - c) zero_le_one]
  refine ⟨hl, hu, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]
  have hx : 0 ≤ a * b * (1 - c) :=
    mul_nonneg (mul_nonneg ha.1 hb.1) (by linarith)
  have hy := mul_nonneg ha.1 hc.1
  have hz := mul_nonneg hb.1 hc.1
  nlinarith [ha.2, hb.2, hc.2]

theorem cavity_summand_taylor {x y a b c δ ε : ℝ}
    (hδ : δ ≤ 1 / 2) (hx : |x| ≤ δ) (hy : |y| ≤ δ)
    (hε : ε ≤ 1 / 2) (ha : a ∈ Set.Icc 0 ε)
    (hb : b ∈ Set.Icc 0 ε) (hc : c ∈ Set.Icc 0 ε) :
    |Real.exp (x + y) / ((1 - a) * (1 - b) * (1 - c)) - 1 - x - y| ≤
      32 * δ ^ 2 + 48 * ε := by
  let P := (1 - a) * (1 - b) * (1 - c)
  have hp := triple_factor_bounds hε ha hb hc
  have hp0 : 0 < P := by dsimp [P]; linarith [hp.1]
  have hδ0 : 0 ≤ δ := (abs_nonneg x).trans hx
  have hε0 : 0 ≤ ε := ha.1.trans ha.2
  have hxy : |x + y| ≤ 2 * δ := (abs_add_le x y).trans (by linarith)
  have he : |Real.exp (x + y) - 1 - (x + y)| ≤ 4 * δ ^ 2 := by
    apply (Real.abs_exp_sub_one_sub_id_le (hxy.trans (by linarith))).trans
    have hh := sq_le_sq.mpr (show |x + y| ≤ |2 * δ| by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hδ0]
      exact hxy)
    nlinarith
  have hlin : |1 + x + y| ≤ 2 := by
    calc
      _ = |1 + (x + y)| := by congr 1; ring
      _ ≤ |(1 : ℝ)| + |x + y| := abs_add_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hPinv : P⁻¹ ≤ 8 := by
    rw [← one_div]
    apply (div_le_iff₀ hp0).mpr
    dsimp [P]
    linarith [hp.1]
  have hPinv0 : 0 ≤ P⁻¹ := inv_nonneg.mpr hp0.le
  calc
    _ = |(Real.exp (x + y) - 1 - (x + y)) * P⁻¹ +
        (1 + x + y) * ((1 - P) * P⁻¹)| := by
      congr 1
      change Real.exp (x + y) / P - 1 - x - y = _
      field_simp [hp0.ne']
      ring
    _ ≤ |Real.exp (x + y) - 1 - (x + y)| * P⁻¹ +
        |1 + x + y| * (|1 - P| * P⁻¹) := by
      simpa only [abs_mul, abs_of_nonneg hPinv0] using abs_add_le
        ((Real.exp (x + y) - 1 - (x + y)) * P⁻¹)
        ((1 + x + y) * ((1 - P) * P⁻¹))
    _ ≤ (4 * δ ^ 2) * 8 + 2 * ((3 * ε) * 8) := by
      apply add_le_add
      · exact mul_le_mul he hPinv hPinv0 (by positivity)
      · exact mul_le_mul hlin
          (mul_le_mul hp.2.2 hPinv hPinv0 (by positivity))
          (mul_nonneg (abs_nonneg _) hPinv0) (by norm_num)
    _ = _ := by ring

theorem cavity_row_error {τ : Type*} (S : Finset τ) (R L : τ → ℝ)
    {D η B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (hdegree : |(S.card : ℝ) / D - 1| ≤ η)
    (hrow : (S.card : ℝ) / D ≤ 2)
    (hterm : ∀ T ∈ S, |R T - 1 - L T| ≤ B) :
    |1 - (1 / D) * (∑ T ∈ S, R T) + (1 / D) * (∑ T ∈ S, L T)| ≤
      η + 2 * B := by
  have heq : 1 - (1 / D) * (∑ T ∈ S, R T) + (1 / D) * (∑ T ∈ S, L T) =
      -(S.card / D - 1) - (1 / D) * (∑ T ∈ S, (R T - 1 - L T)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  rw [heq]
  calc
    _ ≤ |(S.card : ℝ) / D - 1| + |(1 / D) * (∑ T ∈ S, (R T - 1 - L T))| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (-(S.card / D - 1))
        (-((1 / D) * (∑ T ∈ S, (R T - 1 - L T))))
    _ ≤ η + (1 / D) * (S.card * B) := by
      apply add_le_add hdegree
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hD)]
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hD.le)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hterm)
    _ ≤ η + 2 * B := by
      calc
        _ = η + (S.card / D) * B := by ring
        _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right hrow hB]

end SharpTerminalLeave

open Filter MeasureTheory
open scoped Topology

end
end

end OAI
