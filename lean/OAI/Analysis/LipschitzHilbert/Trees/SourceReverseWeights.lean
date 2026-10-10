import OAI.Analysis.LipschitzHilbert.Estimates.IntGeometricSum

namespace OAI

/-! Numerical weights for the bounded-input, unequal-measure estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def reverseThresholdWeight (ratio eta : ℝ) : ℝ :=
  min 1 (Real.sqrt (eta/ratio))*min 1 eta*(1+eta^(-(1/20:ℝ)))/eta

def reverseThresholdRatio : ℝ := (2:ℝ)^(-(1/20:ℝ))

theorem reverseThresholdRatio_pos : 0<reverseThresholdRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem reverseThresholdRatio_lt_one : reverseThresholdRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem reverse_density_factor {eta : ℝ} (heta : 0<eta) :
    min 1 eta*(1+eta^(-(1/20:ℝ)))/eta≤2*eta^(-(1/20:ℝ)) := by
  by_cases h : eta≤1
  · rw [min_eq_right h,mul_div_cancel_left₀ _ heta.ne']
    have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos heta h (by norm_num : -(1/20:ℝ)≤0)
    linarith
  · have h1 : 1≤eta := le_of_not_ge h
    rw [min_eq_left h1,one_mul]
    calc
      _ ≤ 2/eta := div_le_div_of_nonneg_right
        (by linarith [Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : -(1/20:ℝ)≤0)]) heta.le
      _ = 2*eta^(-(1:ℝ)) := by rw [Real.rpow_neg_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : -(1:ℝ)≤ -(1/20:ℝ))) (by norm_num)

theorem reverseThresholdWeight_le_shape {ratio eta : ℝ} (heta : 0<eta) :
    reverseThresholdWeight ratio eta≤
      2*(min 1 (Real.sqrt (eta/ratio))*eta^(-(1/20:ℝ))) := by
  have h := mul_le_mul_of_nonneg_left (reverse_density_factor heta)
    (le_min zero_le_one (Real.sqrt_nonneg (eta/ratio)))
  convert h using 1 <;> (try unfold reverseThresholdWeight) <;> ring

theorem reverse_shape_small {x : ℝ} (hx : 0<x) (hsmall : x≤1) :
    min 1 (Real.sqrt x)*x^(-(1/20:ℝ))≤x^(1/20:ℝ) := by
  calc
    _ ≤ Real.sqrt x*x^(-(1/20:ℝ)) := mul_le_mul_of_nonneg_right
      (min_le_right _ _) (Real.rpow_nonneg hx.le _)
    _ = x^(9/20:ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add hx]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hx hsmall (by norm_num)

theorem reverse_shape_dyadic (k : ℤ) :
    min 1 (Real.sqrt ((2:ℝ)^k))*((2:ℝ)^k)^(-(1/20:ℝ))≤reverseThresholdRatio^k.natAbs := by
  cases k with
  | ofNat n =>
    have h : min 1 (Real.sqrt ((2:ℝ)^n))*((2:ℝ)^n)^(-(1/20:ℝ))≤
        ((2:ℝ)^n)^(-(1/20:ℝ)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (min_le_left 1 (Real.sqrt ((2:ℝ)^n))) (Real.rpow_nonneg (by positivity) (-(1/20:ℝ)))
    change min 1 (Real.sqrt ((2:ℝ)^n))*((2:ℝ)^n)^(-(1/20:ℝ))≤reverseThresholdRatio^n
    exact h.trans_eq (Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2) _ _).symm
  | negSucc n =>
    have he : (2:ℝ)^Int.negSucc n=((2:ℝ)^(n+1))⁻¹ := zpow_negSucc _ _
    have hsmall : (2:ℝ)^Int.negSucc n≤1 := by
      rw [he]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h := reverse_shape_small (zpow_pos (by norm_num : (0:ℝ)<2) _) hsmall
    have hp : ((2:ℝ)^Int.negSucc n)^(1/20:ℝ)=reverseThresholdRatio^(n+1) := by
      rw [he,←Real.rpow_neg_eq_inv_rpow,←Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
      rfl
    simpa only [hp,Int.natAbs_negSucc] using h

theorem reverse_scale_power_le {ratio scale : ℝ} (hr : 0<ratio) (hs : 0<scale)
    (hupper : ratio≤2*scale) :
    scale^(-(1/20:ℝ))≤2*ratio^(-(1/20:ℝ)) := by
  have hp : (2*scale)^(-(1/20:ℝ))≤ratio^(-(1/20:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr hupper (by norm_num)
  have htwo : (2:ℝ)^(1/20:ℝ)≤2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤2) (by norm_num : (1/20:ℝ)≤1)
  have heq : scale^(-(1/20:ℝ))=(2:ℝ)^(1/20:ℝ)*(2*scale)^(-(1/20:ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hs.le,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    rw [←mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos (by norm_num) (1/20:ℝ)).ne',one_mul]
  calc
    _ = _ := heq
    _ ≤ (2:ℝ)^(1/20:ℝ)*ratio^(-(1/20:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hr.le _)

theorem reverseThresholdWeight_scale {ratio scale x : ℝ}
    (hr : 0<ratio) (hs : 0<scale) (hx : 0<x)
    (hlo : scale≤ratio) (hhi : ratio≤2*scale) :
    reverseThresholdWeight ratio (scale*x)≤
      4*ratio^(-(1/20:ℝ))*(min 1 (Real.sqrt x)*x^(-(1/20:ℝ))) := by
  have heta : 0<scale*x := mul_pos hs hx
  have hdiv : scale*x/ratio≤x := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have hm : min 1 (Real.sqrt (scale*x/ratio))≤min 1 (Real.sqrt x) :=
    min_le_min_left 1 (Real.sqrt_le_sqrt hdiv)
  have hpow : (scale*x)^(-(1/20:ℝ))≤2*ratio^(-(1/20:ℝ))*x^(-(1/20:ℝ)) := by
    rw [Real.mul_rpow hs.le hx.le]
    exact mul_le_mul_of_nonneg_right (reverse_scale_power_le hr hs hhi) (Real.rpow_nonneg hx.le _)
  calc
    _ ≤ 2*(min 1 (Real.sqrt (scale*x/ratio))*(scale*x)^(-(1/20:ℝ))) :=
      reverseThresholdWeight_le_shape heta
    _ ≤ 2*(min 1 (Real.sqrt x)*(2*ratio^(-(1/20:ℝ))*x^(-(1/20:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hm hpow (Real.rpow_nonneg heta.le _) (le_min zero_le_one (Real.sqrt_nonneg x))
    _ = _ := by ring

theorem reverseThreshold_dyadic_majorant {ratio : ℝ} (hr : 0<ratio) :
    ∃ a : ℤ, ∀ k : ℤ, reverseThresholdWeight ratio ((2:ℝ)^k)≤
      4*ratio^(-(1/20:ℝ))*reverseThresholdRatio^(k-a).natAbs := by
  obtain ⟨a,ha⟩ := exists_mem_Ico_zpow hr (by norm_num : (1:ℝ)<2)
  have hs : (0:ℝ)<2^a := zpow_pos (by norm_num) a
  have hupper : ratio≤2*(2:ℝ)^a := by
    have h := ha.2.le
    rw [zpow_add₀ (by norm_num),zpow_one] at h
    nlinarith
  refine ⟨a,?_⟩
  intro k
  have hsplit : (2:ℝ)^k=(2:ℝ)^a*(2:ℝ)^(k-a) := by
    rw [←zpow_add₀ (by norm_num)]
    congr 1
    omega
  rw [hsplit]
  exact (reverseThresholdWeight_scale hr hs (zpow_pos (by norm_num) (k-a)) ha.1 hupper).trans
    (mul_le_mul_of_nonneg_left (reverse_shape_dyadic (k-a)) (by positivity))

theorem reverseThreshold_finite_sum {ratio : ℝ} (hr : 0<ratio) (S : Finset ℤ) :
    (∑ k∈S, reverseThresholdWeight ratio ((2:ℝ)^k))≤
      (8/(1-reverseThresholdRatio))*ratio^(-(1/20:ℝ)) := by
  obtain ⟨a,ha⟩ := reverseThreshold_dyadic_majorant hr
  calc
    _ ≤ ∑ k∈S, (4*ratio^(-(1/20:ℝ)))*reverseThresholdRatio^(k-a).natAbs :=
      Finset.sum_le_sum (fun k _ => ha k)
    _ = (4*ratio^(-(1/20:ℝ)))*∑ k∈S, reverseThresholdRatio^(k-a).natAbs := by rw [Finset.mul_sum]
    _ ≤ (4*ratio^(-(1/20:ℝ)))*(2/(1-reverseThresholdRatio)) :=
      mul_le_mul_of_nonneg_left (int_geometric_shift_sum_le reverseThresholdRatio_pos.le
        reverseThresholdRatio_lt_one S a) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
