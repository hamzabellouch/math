import OAI.Geometry.Relativity.CKS.CollarNullMap

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def ratioResidual (p : MomentumInput) : ℝ :=
  ((mc p 1).1-(mc p 0).1-(mc p 4).1-mz p^3*(mc p 0).1*(mc p 4).1)/
    (normalizedSpeed p*nullD p)
lemma ratioResidual_smooth {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    ContDiffAt ℝ ∞ ratioResidual p := by
  have hs : normalizedSpeed p ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne' hp.1.2
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput =>
    (mc p 1).1-(mc p 0).1-(mc p 4).1-mz p^3*(mc p 0).1*(mc p 4).1) p).div
      (normalizedSpeed_smooth.contDiffAt.mul nullD_smooth.contDiffAt) (mul_ne_zero hs hp.2)
lemma nullRatio_factor {p : MomentumInput} (hp : p ∈ nullMomentumRegion) :
    nullRatio p = 1/Real.sqrt (1+mz p^2)+mz p^3*ratioResidual p := by
  have hs : Real.sqrt (1+mz p^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have ha := hp.1.2
  have hd : 1+mz p^3*(mc p 4).1 ≠ 0 := hp.2
  unfold nullRatio ratioResidual normalizedSpeed nullD
  field_simp
  ring
lemma inverse_hyperbolic_ratio (z : ℝ) :
    1/Real.sqrt (1+z^2)-1 = -z^2/(Real.sqrt (1+z^2)*(Real.sqrt (1+z^2)+1)) := by
  have hs : Real.sqrt (1+z^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs1 : Real.sqrt (1+z^2)+1 ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show 0 ≤ 1+z^2 by positivity)
  field_simp
  nlinarith
lemma inverse_hyperbolic_ratio_bound (z : ℝ) :
    |1/Real.sqrt (1+z^2)-1| ≤ z^2 := by
  rw [inverse_hyperbolic_ratio,abs_div,abs_neg,abs_of_nonneg (sq_nonneg z),
    abs_of_pos (by positivity : 0 < Real.sqrt (1+z^2)*(Real.sqrt (1+z^2)+1))]
  apply div_le_self (sq_nonneg z)
  have hs : 1 ≤ Real.sqrt (1+z^2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg z])
  nlinarith
lemma nullRatio_bound {p : MomentumInput} (hp : p ∈ nullMomentumRegion)
    {r B : ℝ} (hr : 1 ≤ r) (hz : mz p = 1/r) (hB : 0 ≤ B)
    (hb : |ratioResidual p| ≤ B) : |nullRatio p-1| ≤ (1+B)/r^2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hzr : 0 ≤ mz p := by rw [hz]; positivity
  rw [nullRatio_factor hp]
  have he : 1/Real.sqrt (1+mz p^2)+mz p^3*ratioResidual p-1 =
      (1/Real.sqrt (1+mz p^2)-1)+mz p^3*ratioResidual p := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (pow_nonneg hzr 3)]
  calc
    _ ≤ mz p^2+mz p^3*B := add_le_add (inverse_hyperbolic_ratio_bound _) (by gcongr)
    _ = 1/r^2+B/r^3 := by rw [hz]; ring
    _ ≤ 1/r^2+B/r^2 := by gcongr; norm_num
    _ = _ := by ring
lemma nullRatio_difference {p q : MomentumInput} (hp : p ∈ nullMomentumRegion)
    (hq : q ∈ nullMomentumRegion) (hz : mz p = mz q) :
    nullRatio p-nullRatio q = mz p^3*(ratioResidual p-ratioResidual q) := by
  rw [nullRatio_factor hp,nullRatio_factor hq,← hz]
  ring

end
end CKSAngularGeometry

end

end OAI
