import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def clipFunction (t : ℝ) : ℝ := (max 1 (Real.sqrt t))⁻¹

lemma continuous_clipFunction : Continuous clipFunction := by
  apply Continuous.inv₀
  · exact continuous_const.max Real.continuous_sqrt
  · intro t
    have : 0 < max (1 : ℝ) (Real.sqrt t) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact ne_of_gt this

lemma clipFunction_nonneg (t : ℝ) : 0 ≤ clipFunction t := by
  unfold clipFunction
  positivity

lemma clipFunction_le_one (t : ℝ) : clipFunction t ≤ 1 := by
  unfold clipFunction
  exact inv_le_one_of_one_le₀ (le_max_left _ _)

def cstarClip (v : B) : B := v*cfc clipFunction (star v*v)

lemma star_mul_function_square (v : B) (f : ℝ → ℝ) (hf : Continuous f) :
    star (v*cfc f (star v*v))*(v*cfc f (star v*v))=
      cfc (fun t => f t*t*f t) (star v*v) := by
  have ha : IsSelfAdjoint (star v*v) := (star_mul_self_nonneg v).isSelfAdjoint
  rw [star_mul, (cfc_predicate f (star v*v)).star_eq]
  calc
    (cfc f (star v*v)*star v)*(v*cfc f (star v*v)) =
        (cfc f (star v*v)*(star v*v))*cfc f (star v*v) := by noncomm_ring
    _ = (cfc f (star v*v)*cfc (fun t : ℝ => t) (star v*v))*cfc f (star v*v) := by
      rw [cfc_id' ℝ (star v*v)]
    _ = cfc (fun t => f t*t*f t) (star v*v) := by
      rw [← cfc_mul f (fun t : ℝ => t) (star v*v) hf.continuousOn continuous_id.continuousOn,
        ← cfc_mul (fun t : ℝ => f t*t) f (star v*v) (hf.mul continuous_id).continuousOn hf.continuousOn]

lemma clip_scalar_norm (t : ℝ) (ht : 0 ≤ t) :
    ‖clipFunction t*t*clipFunction t‖ ≤ 1 := by
  have hsq := Real.sq_sqrt ht
  have hs := Real.sqrt_nonneg t
  have hf := clipFunction_nonneg t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold clipFunction
  by_cases ht1 : Real.sqrt t ≤ 1
  · rw [max_eq_left ht1, inv_one, one_mul, mul_one]
    nlinarith
  · have hs1 : 1 < Real.sqrt t := lt_of_not_ge ht1
    rw [max_eq_right hs1.le]
    have hs0 : Real.sqrt t ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs1)
    have : (Real.sqrt t)⁻¹*t*(Real.sqrt t)⁻¹=1 := by
      calc
        _ = (Real.sqrt t)⁻¹*(Real.sqrt t)^2*(Real.sqrt t)⁻¹ := by rw [hsq]
        _ = 1 := by field_simp
    exact this.le

lemma norm_cstarClip_le (v : B) : ‖cstarClip v‖ ≤ 1 := by
  have ha : 0 ≤ star v*v := star_mul_self_nonneg v
  have hn : ‖star (cstarClip v)*cstarClip v‖ ≤ 1 := by
    rw [cstarClip, star_mul_function_square v clipFunction continuous_clipFunction]
    apply norm_cfc_le zero_le_one
    intro t ht
    exact clip_scalar_norm t (spectrum_nonneg_of_nonneg ha ht)
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (cstarClip v)]

lemma clip_scalar_difference_bound (t M : ℝ) (ht : 0 ≤ t) (hM : 0 ≤ M) (htM : t ≤ M^2) :
    ‖(1-clipFunction t)*t*(1-clipFunction t)‖ ≤ (max (M-1) 0)^2 := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht
  have hsM : Real.sqrt t ≤ M := by nlinarith
  have hg : 0 ≤ 1-clipFunction t := sub_nonneg.mpr (clipFunction_le_one t)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold clipFunction
  by_cases ht1 : Real.sqrt t ≤ 1
  · rw [max_eq_left ht1, inv_one, sub_self, zero_mul, zero_mul]
    positivity
  · have hs1 : 1 < Real.sqrt t := lt_of_not_ge ht1
    rw [max_eq_right hs1.le]
    have hs0 : Real.sqrt t ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs1)
    have hid : (1-(Real.sqrt t)⁻¹)*t*(1-(Real.sqrt t)⁻¹)=(Real.sqrt t-1)^2 := by
      calc
        _ = (1-(Real.sqrt t)⁻¹)*(Real.sqrt t)^2*(1-(Real.sqrt t)⁻¹) := by rw [hsq]
        _ = (Real.sqrt t-1)^2 := by field_simp
    rw [hid, max_eq_left (by linarith : 0 ≤ M-1)]
    nlinarith

omit [PartialOrder B] [StarOrderedRing B] in
lemma sub_cstarClip (v : B) :
    v-cstarClip v=v*cfc (fun t : ℝ => 1-clipFunction t) (star v*v) := by
  rw [cfc_sub (fun _ : ℝ => 1) clipFunction (star v*v) continuous_const.continuousOn
    continuous_clipFunction.continuousOn, cfc_const_one ℝ (star v*v), mul_sub, mul_one]
  rfl

lemma norm_sub_cstarClip_le (v : B) : ‖v-cstarClip v‖ ≤ max (‖v‖-1) 0 := by
  nontriviality B
  have ha : 0 ≤ star v*v := star_mul_self_nonneg v
  have hn : ‖star (v-cstarClip v)*(v-cstarClip v)‖ ≤ (max (‖v‖-1) 0)^2 := by
    rw [sub_cstarClip, star_mul_function_square v (fun t : ℝ => 1-clipFunction t)
      (continuous_const.sub continuous_clipFunction)]
    apply norm_cfc_le (sq_nonneg _)
    intro t ht
    apply clip_scalar_difference_bound t ‖v‖ (spectrum_nonneg_of_nonneg ha ht) (norm_nonneg v)
    have hh := spectrum.norm_le_norm_of_mem ht
    rw [Real.norm_eq_abs, abs_of_nonneg (spectrum_nonneg_of_nonneg ha ht),
      CStarRing.norm_star_mul_self] at hh
    nlinarith
  rw [CStarRing.norm_star_mul_self] at hn
  have hm : 0 ≤ max (‖v‖-1) 0 := le_max_right _ _
  nlinarith [norm_nonneg (v-cstarClip v)]

lemma map_cstarClip {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (π : B →⋆ₐ[ℂ] C) (v : B) : π (cstarClip v)=cstarClip (π v) := by
  have ha : IsSelfAdjoint (star v*v) := (star_mul_self_nonneg v).isSelfAdjoint
  rw [cstarClip, map_mul, π.map_cfc clipFunction (star v*v)
    continuous_clipFunction.continuousOn (by fun_prop) ha (ha.map π), map_mul, map_star]
  rfl

end

end WeakPureInfiniteness
end

end OAI
