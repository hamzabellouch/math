import OAI.Analysis.TriangularHilbert.MeshMass

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_neg (σ x : ℝ) : density σ (-x) = density σ x := by
  simp [density]

lemma density_le_zero (σ x : ℝ) : density σ x ≤ density σ 0 := by
  by_cases hs : 0 < σ
  · unfold density
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    simp only [zero_pow (by decide : 2 ≠ 0),neg_zero,zero_div]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by positivity)
  · have he : Real.sqrt (2*Real.pi*σ) = 0 := Real.sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hs))
    simp [density,he]

lemma density_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b p : ℝ) :
    density s (a-p)*density t (b-p) =
      density (s+t) (a-b)*density (s*t/(s+t)) (p-(t*a+s*b)/(s+t)) := by
  have hst : s+t ≠ 0 := (add_pos hs ht).ne'
  have hn : Real.sqrt (2*Real.pi*s)*Real.sqrt (2*Real.pi*t) =
      Real.sqrt (2*Real.pi*(s+t))*Real.sqrt (2*Real.pi*(s*t/(s+t))) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*s),← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*(s+t))]
    congr 1
    field_simp
  have he : -(a-p)^2/(2*s) + -(b-p)^2/(2*t) =
      -(a-b)^2/(2*(s+t)) + -(p-(t*a+s*b)/(s+t))^2/(2*(s*t/(s+t))) := by
    field_simp
    ring
  unfold density
  calc
    _ = (Real.sqrt (2*Real.pi*s)*Real.sqrt (2*Real.pi*t))⁻¹ *
        Real.exp (-(a-p)^2/(2*s) + -(b-p)^2/(2*t)) := by rw [mul_inv,Real.exp_add]; ring
    _ = _ := by rw [hn,he,mul_inv,Real.exp_add]; ring

lemma integral_density_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    (∫ p, density s (a-p)*density t (b-p)) = density (s+t) (a-b) := by
  simp_rw [density_product hs ht]
  rw [integral_const_mul,integral_sub_right_eq_self,integral_density (by positivity),mul_one]
end
end TriangularHilbert.Heat
end

end OAI
