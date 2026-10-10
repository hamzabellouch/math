import OAI.Analysis.TriangularHilbert.HeatInsert

namespace OAI

section

namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma gaussian_exponent_le {σ b : ℝ} (hσ : 0 < σ) (hσb : σ ≤ b) (u p : ℝ) :
    -(u-p)^2 / (2*σ) ≤ u^2/(2*b) - p^2/(4*b) := by
  have hb : 0 < b := hσ.trans_le hσb
  calc
    _ ≤ -(u-p)^2 / (2*b) := by
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))
    _ = (-2*(u-p)^2)/(4*b) := by field_simp; ring
    _ ≤ (2*u^2-p^2)/(4*b) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (p - 2*u)]
    _ = _ := by field_simp; ring

lemma weight_le_gaussian {h a σ b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (haσ : a ≤ σ) (hσb : σ ≤ b) (u p : ℝ) :
    weight h u p σ ≤
      (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b))) *
        Real.exp (-p^2/(4*b)) := by
  have hσ := ha.trans_le haσ
  have hn : (Real.sqrt (2*Real.pi*σ))⁻¹ ≤ (Real.sqrt (2*Real.pi*a))⁻¹ := by
    simp only [← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    exact Real.sqrt_le_sqrt (by gcongr)
  have he := Real.exp_le_exp.mpr (gaussian_exponent_le hσ hσb u p)
  unfold weight density
  calc
    _ ≤ h * ((Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b)-p^2/(4*b))) := by
      gcongr
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf

lemma rootWeight_le_gaussian {h a σ b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (haσ : a ≤ σ) (hσb : σ ≤ b) (u p : ℝ) :
    Real.sqrt (weight h u p σ) ≤
      Real.sqrt (h * (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (u^2/(2*b))) *
        Real.exp (-p^2/(8*b)) := by
  have hh' := Real.sqrt_le_sqrt (weight_le_gaussian hh ha haσ hσb u p)
  rw [Real.sqrt_mul (by positivity), ← Real.exp_half] at hh'
  convert! hh' using 1
  congr 2
  field_simp
  ring

lemma score_le_linear {a σ : ℝ} (ha : 0 < a) (haσ : a ≤ σ) (u p : ℝ) :
    |score u p σ| ≤ (|u|+|p|)/a := by
  unfold score
  rw [abs_div, abs_of_pos (ha.trans_le haσ)]
  exact (div_le_div_of_nonneg_right (by simpa using abs_sub_le u 0 p) (ha.trans_le haσ).le).trans
    (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _)) ha haσ)

lemma integrable_one_add_sq_sq_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => (1+x^2)^2 * Real.exp (-b*x^2)) := by
  have h0 : Integrable (fun x : ℝ => Real.exp (-b*x^2)) := by
    simpa using (integrable_rpow_mul_exp_neg_mul_sq hb (s := 0) (by norm_num))
  have h2 : Integrable (fun x : ℝ => x^2 * Real.exp (-b*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (s := (2:ℕ)) (by norm_num))
  have h4 : Integrable (fun x : ℝ => x^4 * Real.exp (-b*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (s := (4:ℕ)) (by norm_num))
  convert! h0.add ((h2.const_mul 2).add h4) using 1
  ext x
  dsimp
  ring

def planeGaussian (b : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-b*(z.1^2 + z.2^2))

def planePoly (z : ℝ × ℝ) : ℝ := (1+z.1^2) * (1+z.2^2)

lemma planeGaussian_pos (b : ℝ) (z : ℝ × ℝ) : 0 < planeGaussian b z := Real.exp_pos _
lemma planeGaussian_le_one {b : ℝ} (hb : 0 ≤ b) (z : ℝ × ℝ) : planeGaussian b z ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma one_le_planePoly (z : ℝ × ℝ) : 1 ≤ planePoly z := by
  unfold planePoly
  nlinarith [sq_nonneg z.1, sq_nonneg z.2, mul_nonneg (sq_nonneg z.1) (sq_nonneg z.2)]
lemma planePoly_nonneg (z : ℝ × ℝ) : 0 ≤ planePoly z := (by norm_num : (0:ℝ) ≤ 1).trans (one_le_planePoly z)

lemma integrable_planePoly_sq_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun z => planePoly z ^2 * planeGaussian b z) := by
  have hh := (integrable_one_add_sq_sq_gaussian hb).mul_prod (integrable_one_add_sq_sq_gaussian hb)
  convert! hh using 1
  ext z
  simp only [planePoly, planeGaussian]
  rw [show -b * (z.1^2+z.2^2) = -b*z.1^2 + -b*z.2^2 by ring, Real.exp_add]
  ring

end
end TriangularHilbert.Heat
end

end OAI
