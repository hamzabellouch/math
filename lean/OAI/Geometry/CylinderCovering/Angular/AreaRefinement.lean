import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
namespace TriangularCovering
open Set MeasureTheory
open scoped Interval

lemma d_lipschitz_sharp {a q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1) :
    |d a - d q| ≤ (3 / 8 : ℝ) * |a - q| := by
  have ha2 : a ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp ha).1, (abs_le.mp ha).2]
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have has : |a + q| ≤ 2 := (abs_add_le _ _).trans (by linarith only [ha, hq])
  have hs0 : 0 ≤ 1 + a ^ 2 + q ^ 2 := by positivity
  have hs1 : 1 + a ^ 2 + q ^ 2 ≤ 3 := by linarith only [ha2, hq2]
  have hid : d a - d q = (a - q) * ((a + q) * (1 + a ^ 2 + q ^ 2) / 16) := by
    dsimp [d]
    ring
  have hfactor : |(a + q) * (1 + a ^ 2 + q ^ 2) / 16| ≤ (3 / 8 : ℝ) := by
    rw [abs_div, abs_mul, abs_of_nonneg hs0]
    norm_num
    have hp := mul_le_mul has hs1 hs0 (by norm_num : (0 : ℝ) ≤ 2)
    linarith only [hp]
  rw [hid, abs_mul, mul_comm (3 / 8 : ℝ)]
  exact mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)

lemma cutoffCoeff_error_sharp {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hq : a ≤ q ∧ q ≤ b) :
    |cutoffCoeff a b - (η + d q)| ≤ (3 / 8 : ℝ) * (b - a) := by
  have hqab : |q| ≤ 1 := abs_le.mpr
    ⟨(abs_le.mp ha).1.trans hq.1, hq.2.trans (abs_le.mp hb).2⟩
  have h1 := d_lipschitz_sharp ha hqab
  have h2 := d_lipschitz_sharp hb hqab
  rw [abs_of_nonpos (sub_nonpos.mpr hq.1)] at h1
  rw [abs_of_nonneg (sub_nonneg.mpr hq.2)] at h2
  have hlo := d_le_max_endpoints hq.1 hq.2
  have hhi : max (d a) (d b) ≤ d q + (3 / 8 : ℝ) * (b - a) := by
    apply max_le <;> linarith only [(abs_le.mp h1).2, (abs_le.mp h2).2, hq.1, hq.2]
  dsimp [cutoffCoeff]
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, hq.1, hq.2]

lemma density_error_sharp {a b q : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hq : a ≤ q ∧ q ≤ b) :
    |cutoffCoeff a b - speedSq a b / 8 - areaDensity q| ≤ (b - a) / 2 := by
  have hqab : |q| ≤ 1 := abs_le.mpr
    ⟨(abs_le.mp ha).1.trans hq.1, hq.2.trans (abs_le.mp hb).2⟩
  have hc := coeff_bounds ha hb
  have hal : |alpha a b| ≤ 1 / 2 := by
    rw [abs_of_nonneg hc.1]
    exact hc.2.1
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith only [(abs_le.mp hqab).1, (abs_le.mp hqab).2]
  have hql : |(1 + q ^ 2) / 4| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by positivity)]
    linarith only [hq2]
  have haq := sq_error hal hql (alpha_error ha hqab hq.1 hq.2)
  have hqr : |q / 2| ≤ 1 / 2 := by
    rw [abs_div]
    norm_num
    linarith only [hqab]
  have hbq := sq_error hc.2.2.1 hqr (beta_error hq.1 hq.2)
  have hspeed : |speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2)| ≤ b - a := by
    have hid : speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2) =
        ((alpha a b) ^ 2 - ((1 + q ^ 2) / 4) ^ 2) +
          2 * ((beta a b) ^ 2 - (q / 2) ^ 2) := by
      dsimp [speedSq]
      ring
    rw [hid]
    have h := abs_add_le ((alpha a b) ^ 2 - ((1 + q ^ 2) / 4) ^ 2)
      (2 * ((beta a b) ^ 2 - (q / 2) ^ 2))
    rw [abs_mul] at h
    norm_num at h
    linarith only [h, haq, hbq]
  have hM := cutoffCoeff_error_sharp ha hb hq
  have hid : cutoffCoeff a b - speedSq a b / 8 - areaDensity q =
      (cutoffCoeff a b - (η + d q)) -
        (speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2)) / 8 := by
    dsimp [areaDensity]
    ring
  rw [hid]
  have hr := abs_add_le (cutoffCoeff a b - (η + d q))
    (-((speedSq a b - (((1 + q ^ 2) / 4) ^ 2 + 2 * (q / 2) ^ 2)) / 8))
  rw [← sub_eq_add_neg, abs_neg] at hr
  rw [abs_div] at hr
  norm_num at hr
  linarith only [hr, hM, hspeed]

lemma interval_density_error_sharp {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≤ b) :
    |(b - a) * (cutoffCoeff a b - speedSq a b / 8) -
      (∫ q in a..b, areaDensity q)| ≤ (b - a) ^ 2 / 2 := by
  have hu : ∀ q ∈ Ι a b,
      ‖cutoffCoeff a b - speedSq a b / 8 - areaDensity q‖ ≤ (b - a) / 2 := by
    intro q hq
    rw [Set.uIoc_of_le hab] at hq
    simpa only [Real.norm_eq_abs] using density_error_sharp ha hb ⟨hq.1.le, hq.2⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hu
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => cutoffCoeff a b - speedSq a b / 8)
    (g := areaDensity) (continuous_const.intervalIntegrable _ _)
    (continuous_areaDensity.intervalIntegrable _ _), intervalIntegral.integral_const,
    Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg (sub_nonneg.mpr hab)] at h
  nlinarith only [h]

lemma coefficientSum_error_sharp {N : ℕ} (hN : 0 < N) :
    |coefficientSum N + 13 / 6000| ≤ step N := by
  have hi := integral_mesh_sum hN
  have hid : coefficientSum N + 13 / 6000 =
      ∑ j : Fin N, (step N * (cutoffCoeff (mesh N j) (mesh N (j + 1)) -
        speedSq (mesh N j) (mesh N (j + 1)) / 8) -
        ∫ q in mesh N j..mesh N (j + 1), areaDensity q) := by
    rw [Finset.sum_sub_distrib, hi]
    dsimp [coefficientSum]
    ring
  rw [hid]
  calc
    _ ≤ ∑ j : Fin N, |step N * (cutoffCoeff (mesh N j) (mesh N (j + 1)) -
        speedSq (mesh N j) (mesh N (j + 1)) / 8) -
        ∫ q in mesh N j..mesh N (j + 1), areaDensity q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, (step N) ^ 2 / 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := interval_density_error_sharp (mesh_abs_le hN j.isLt.le)
        (mesh_abs_le hN j.isLt)
        (le_of_lt (by have := mesh_succ N j; have := step_pos hN; linarith))
      simpa only [mesh_succ] using h
    _ = step N := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (N : ℝ) * ((step N) ^ 2 / 2) = ((N : ℝ) * step N) * step N / 2 := by ring
        _ = step N := by rw [count_step hN]; ring

end TriangularCovering

end

end OAI
