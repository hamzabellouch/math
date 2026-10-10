import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.MixedThreeJets

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def radiusPower (n : ℝ) (x : Point) : ℝ :=
  letI := pointDimension_neZero
  Real.exp (n*x 0)
lemma radiusPower_pos (n : ℝ) (x : Point) : 0 < radiusPower n x := Real.exp_pos _
lemma radiusPower_smooth (n : ℝ) : ContDiff ℝ ∞ (radiusPower n) := by unfold radiusPower; fun_prop
lemma radiusPower_diff (n : ℝ) (m : ℕ) (x : Point) : ContDiffAt ℝ m (radiusPower n) x :=
  ((radiusPower_smooth n).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt
lemma basis_rad_abs (a : I) : |basis a 0| ≤ 1 := by
  simp only [basis,Pi.single_apply]
  split_ifs <;> norm_num
lemma D_radiusPower (n : ℝ) (a : I) :
    D (basis a) (radiusPower n) = fun x => (n*basis a 0)*radiusPower n x := by
  funext x
  have hc : DifferentiableAt ℝ (fun y : Point => y 0) x := by fun_prop
  unfold radiusPower
  rw [D_comp_real (basis a) (Real.differentiableAt_exp) (hc.const_mul n),
    Real.deriv_exp,D_const_mul (basis a) n hc]
  change Real.exp (n*x 0) * (n*D (basis a) (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ) x) = _
  rw [D_clm]
  simp only [ContinuousLinearMap.proj_apply]
  ring

lemma actual_radiusPower (n : ℝ) (x : Point) :
    actualScalarJet (radiusPower n) x =
    (radiusPower n x, (fun a => (n*basis a 0)*radiusPower n x),
      fun a b => (n*basis b 0)*((n*basis a 0)*radiusPower n x)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext a
    exact congrFun (D_radiusPower n a) x
  · funext a b
    change D (basis a) (D (basis b) (radiusPower n)) x = _
    rw [D_radiusPower,D_const_mul (basis a) _ ((radiusPower_diff n 2 x).differentiableAt (by norm_num)),D_radiusPower]

lemma radiusPower_two_norm (n : ℝ) (x : Point) :
    ‖actualScalarJet (radiusPower n) x‖ ≤ (max 1 |n|)^2*radiusPower n x := by
  let N : ℝ := max 1 |n|
  have hN : 1 ≤ N := le_max_left _ _
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hn : |n| ≤ N := le_max_right _ _
  have hR : 0 ≤ radiusPower n x := (radiusPower_pos n x).le
  have hc (a : I) : |n*basis a 0| ≤ N := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (basis_rad_abs a) (abs_nonneg n)).trans (by simpa using hn)
  have hN2 : N ≤ N^2 := by nlinarith
  rw [actual_radiusPower]
  apply norm_prod_le_iff.mpr
  constructor
  · change |radiusPower n x| ≤ _
    rw [abs_of_nonneg hR]
    nlinarith [mul_nonneg (sq_nonneg N) hR]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_right ((hc a).trans hN2) hR
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro b
    rw [Real.norm_eq_abs,abs_mul,abs_mul (n*basis a 0),abs_of_nonneg hR]
    calc
      _ ≤ N*(N*radiusPower n x) := mul_le_mul (hc b) (mul_le_mul_of_nonneg_right (hc a) hR) (by positivity) hN0
      _ = N^2*radiusPower n x := by ring

lemma radiusPower_three_norm (n : ℝ) (x : Point) :
    ‖actualThreeJet (radiusPower n) x‖ ≤ (max 1 |n|)^3*radiusPower n x := by
  let N : ℝ := max 1 |n|
  have hN : 1 ≤ N := le_max_left _ _
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hR : 0 ≤ radiusPower n x := (radiusPower_pos n x).le
  have hn : |n| ≤ N := le_max_right _ _
  have hN23 : N^2 ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
  apply norm_prod_le_iff.mpr
  constructor
  · exact (radiusPower_two_norm n x).trans (mul_le_mul_of_nonneg_right hN23 hR)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  change ‖actualScalarJet (D (basis a) (radiusPower n)) x‖ ≤ _
  rw [D_radiusPower,actualScalarJet_smul _ (radiusPower_diff n 2 x),norm_smul,Real.norm_eq_abs]
  have hc : |n*basis a 0| ≤ N := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (basis_rad_abs a) (abs_nonneg n)).trans (by simpa using hn)
  calc
    _ ≤ N*(N^2*radiusPower n x) := mul_le_mul hc (radiusPower_two_norm n x) (norm_nonneg _) hN0
    _ = N^3*radiusPower n x := by ring

lemma inverse_radius_three_norm (x : Point) :
    ‖actualThreeJet (radiusPower (-1)) x‖ ≤ 1/Real.exp (x 0) := by
  simpa only [abs_neg,abs_one,max_self,one_pow,one_mul,radiusPower,neg_one_mul,Real.exp_neg,one_div]
    using radiusPower_three_norm (-1) x

end
end CKSMixedGeometry

end

end OAI
