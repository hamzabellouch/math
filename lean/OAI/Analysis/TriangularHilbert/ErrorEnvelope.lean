import OAI.Analysis.TriangularHilbert.SmoothFormula

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def errorProfile (v : ℝ) : ℝ := kernelProfile v - if 1 < |v| then kernelConstant else 0

def endpointError (r t : ℝ) : ℝ := errorProfile (t/r)/t

lemma kernelProfile_zero : kernelProfile 0 = 0 := by
  unfold kernelProfile kernelConstant
  ring

lemma profile_contDiff : ContDiff ℝ 1 kernelProfile := by
  unfold kernelProfile density
  fun_prop

lemma density_three_six (v : ℝ) :
    density 3 v = Real.sqrt 2*Real.exp (-v^2/12)*density 6 v := by
  have hp : Real.sqrt (2*Real.pi*3) ≠ 0 := by positivity
  have h2 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  unfold density
  rw [show 2*Real.pi*6 = 2*(2*Real.pi*3) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have he : -v^2/(2*3) = -v^2/12 + -v^2/(2*6) := by ring
  rw [he,Real.exp_add]
  field_simp

lemma polynomial_exp_le (v : ℝ) : (v^2/9+1/3)*Real.exp (-v^2/12) ≤ 5/3 := by
  have ha := Real.add_one_le_exp (v^2/12)
  have he : Real.exp (v^2/12)*Real.exp (-v^2/12) = 1 := by
    rw [← Real.exp_add,show v^2/12+-v^2/12=0 by ring,Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_right ha (Real.exp_pos (-v^2/12)).le
  rw [he] at hm
  have hle : Real.exp (-v^2/12) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg v])
  nlinarith

lemma errorProfile_exists_bound : ∃ K : ℝ, 0 < K ∧ ∀ v,
    |errorProfile v| ≤ K*|v| *density 6 v := by
  obtain ⟨L,hL⟩ := profile_contDiff.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1:WithTop ℕ∞) ≠ 0) (convex_Icc (-1:ℝ) 1) (isCompact_Icc (a := (-1:ℝ)) (b := 1))
  let K : ℝ := (L:ℝ)/density 6 1 + 10*Real.sqrt 2
  have hd : 0 < density 6 1 := density_pos (by norm_num) 1
  have hK : 0 < K := add_pos_of_nonneg_of_pos (div_nonneg L.coe_nonneg hd.le) (by positivity)
  refine ⟨K,hK,fun v => ?_⟩
  by_cases hv : 1 < |v|
  · have he : errorProfile v = -2*(v^2/9-1/3)*density 3 v := by
      unfold errorProfile kernelProfile
      rw [ite_eq_left hv]
      ring
    have hab : |v^2/9-1/3| ≤ v^2/9+1/3 := by
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg v],by linarith⟩
    have hb : |errorProfile v| ≤ (10/3)*Real.sqrt 2*density 6 v := by
      rw [he,abs_mul,abs_mul,abs_of_nonneg (density_nonneg (by norm_num) v)]
      norm_num only [abs_neg]
      calc
        _ ≤ 2*(v^2/9+1/3)*density 3 v := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hab (by norm_num)) (density_nonneg (by norm_num) v)
        _ = 2*Real.sqrt 2*((v^2/9+1/3)*Real.exp (-v^2/12))*density 6 v := by rw [density_three_six]; ring
        _ ≤ 2*Real.sqrt 2*(5/3)*density 6 v := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_exp_le v) (by positivity)) (density_nonneg (by norm_num) v)
        _ = _ := by ring
    apply hb.trans
    have hk : 10*Real.sqrt 2 ≤ K := le_add_of_nonneg_left (div_nonneg L.coe_nonneg hd.le)
    apply mul_le_mul_of_nonneg_right _ (density_nonneg (by norm_num) v)
    calc
      (10/3)*Real.sqrt 2 ≤ 10*Real.sqrt 2 := by gcongr; norm_num
      _ ≤ K := hk
      _ ≤ K*|v| := le_mul_of_one_le_right hK.le hv.le
  · have hv' : |v| ≤ 1 := le_of_not_gt hv
    have hmem : v ∈ Set.Icc (-1:ℝ) 1 := abs_le.mp hv'
    have hb : |kernelProfile v| ≤ (L:ℝ)*|v| := by
      have hh := hL.dist_le_mul v hmem 0 (by constructor <;> norm_num)
      simpa only [Real.dist_eq,kernelProfile_zero,sub_zero] using hh
    have hden : density 6 1 ≤ density 6 v := by
      unfold density
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hs : v^2 ≤ 1 := by nlinarith [sq_abs v,abs_nonneg v]
      nlinarith
    unfold errorProfile
    rw [ite_eq_right hv,sub_zero]
    apply hb.trans
    have hk : (L:ℝ) ≤ K*density 6 v := by
      calc
        (L:ℝ) = ((L:ℝ)/density 6 1)*density 6 1 := (div_mul_cancel₀ _ hd.ne').symm
        _ ≤ ((L:ℝ)/density 6 1)*density 6 v := mul_le_mul_of_nonneg_left hden (div_nonneg L.coe_nonneg hd.le)
        _ ≤ K*density 6 v := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by positivity)) (density_nonneg (by norm_num) v)
    nlinarith [mul_le_mul_of_nonneg_right hk (abs_nonneg v)]

def envelopeConstant : ℝ := errorProfile_exists_bound.choose
lemma envelopeConstant_pos : 0 < envelopeConstant := errorProfile_exists_bound.choose_spec.1
lemma errorProfile_bound (v : ℝ) : |errorProfile v| ≤ envelopeConstant*|v| *density 6 v :=
  errorProfile_exists_bound.choose_spec.2 v

lemma endpointError_bound {r : ℝ} (hr : 0 < r) (t : ℝ) :
    |endpointError r t| ≤ envelopeConstant*density (6*r^2) t := by
  by_cases ht : t = 0
  · subst t
    simp only [endpointError,div_zero,abs_zero]
    exact mul_nonneg envelopeConstant_pos.le (density_nonneg (by positivity) _)
  have hd := density_dilation (sq_pos_of_pos hr) (by norm_num : (0:ℝ)<6) t
  rw [Real.sqrt_sq hr.le] at hd
  unfold endpointError
  rw [abs_div]
  apply (div_le_div_of_nonneg_right (errorProfile_bound (t/r)) (abs_nonneg t)).trans_eq
  rw [abs_div,abs_of_pos hr,hd]
  field_simp

end
end TriangularHilbert.Heat
end

end OAI
