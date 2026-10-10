import OAI.Geometry.Relativity.CKS.MixedJetCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma smallNull_remainders_bound {r w A C B D x y z : ℝ}
    (hr : 1 ≤ r) (hw : 0 ≤ w) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hx : |x| ≤ C*A*w) (hy : |y| ≤ B) (hz : |z| ≤ D*A*w/r^3) :
    |x/r^4-2*w*y/(r^6*Real.sqrt r)+z/(2*r^2)| ≤
      (C*A+2*B+D*A)*w/r^4 := by
  have hr0 : 0 < r := by linarith
  have hs1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hpad : |2*w*y/(r^6*Real.sqrt r)| ≤ 2*B*w/r^4 := by
    rw [abs_div,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg hw,abs_of_pos (mul_pos (pow_pos hr0 6) hsr)]
    calc
      _ ≤ 2*w*B/(r^6*Real.sqrt r) := by gcongr
      _ ≤ 2*w*B/r^4 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hr0 4)
        exact (pow_le_pow_right₀ hr (by decide : 4 ≤ 6)).trans
          (le_mul_of_one_le_right (pow_nonneg hr0.le _) hs1)
      _ = _ := by ring
  have hcurv : |z/(2*r^2)| ≤ D*A*w/r^4 := by
    rw [abs_div,abs_of_pos (mul_pos (by norm_num : (0:ℝ) < 2) (pow_pos hr0 2))]
    calc
      _ ≤ (D*A*w/r^3)/(2*r^2) := by gcongr
      _ = D*A*w/(2*r^5) := by ring
      _ ≤ D*A*w/r^4 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hr0 4)
        exact (pow_le_pow_right₀ hr (by decide : 4 ≤ 5)).trans
          (by nlinarith [pow_nonneg hr0.le 5])
  have hres : |x/r^4| ≤ C*A*w/r^4 := by
    rw [abs_div,abs_of_pos (pow_pos hr0 4)]
    exact div_le_div₀ (mul_nonneg (mul_nonneg hC hA) hw) hx (pow_pos hr0 4) le_rfl
  apply (abs_add_le _ _).trans
  have hs : |x/r^4-2*w*y/(r^6*Real.sqrt r)| ≤ |x/r^4|+|2*w*y/(r^6*Real.sqrt r)| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (x/r^4) (-(2*w*y/(r^6*Real.sqrt r)))
  have he : C*A*w/r^4+2*B*w/r^4+D*A*w/r^4 = (C*A+2*B+D*A)*w/r^4 := by ring
  linarith

end
end CKSAngularGeometry

end

end OAI
