import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in

lemma exists_unit_common_kernel (hd : 3 ≤ Module.finrank ℝ E)
    (R T : E →L[ℝ] ℝ) : ∃ w : E, ‖w‖ = 1 ∧ R w = 0 ∧ T w = 0 := by
  classical
  let L : E →ₗ[ℝ] ℝ × ℝ := R.toLinearMap.prod T.toLinearMap
  have hn : ¬Function.Injective L := by
    intro h
    have hh := LinearMap.finrank_le_finrank_of_injective h
    have ht : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
    rw [ht] at hh
    omega
  unfold Function.Injective at hn
  push Not at hn
  obtain ⟨v,z,he,hne⟩ := hn
  have hvz : v-z ≠ 0 := sub_ne_zero.mpr hne
  have hl : L (v-z) = 0 := by rw [map_sub,he,sub_self]
  have hR : R (v-z) = 0 := congrArg Prod.fst hl
  have hT : T (v-z) = 0 := congrArg Prod.snd hl
  refine ⟨‖v-z‖⁻¹ • (v-z),?_,?_,?_⟩
  · simp [norm_smul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvz)]
  · simp only [map_smul,hR,smul_zero]
  · simp only [map_smul,hT,smul_zero]

theorem radial_angular_witness (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2)) :
    ∃ w : E, ‖w‖ = 1 ∧ inner ℝ (a+q • r+e) w = 0 ∧
      R w = 0 ∧ 1/4 ≤ |T w| := by
  obtain ⟨w,hw,hAw,hRw⟩ := exists_unit_common_kernel hd
    (InnerProductSpace.toDual ℝ E (a+q • r+e)) R
  have hAw' : inner ℝ (a+q • r+e) w = 0 := hAw
  have hi : inner ℝ a w = -inner ℝ e w := by
    simpa only [inner_add_left,inner_smul_left,hr,hRw,mul_zero,add_zero,add_eq_zero_iff_eq_neg] using hAw'
  have hib : |inner ℝ a w| ≤ ‖a‖/2 := by
    rw [hi,abs_neg]
    have hh := abs_real_inner_le_norm e w
    rw [hw,mul_one] at hh
    exact hh.trans he
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let c := inner ℝ a w / ‖a‖^2
  let v := w-c • a
  have hav : inner ℝ a v = 0 := by
    simp only [v,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,c]
    field_simp; ring
  have hc : ‖c • a‖ ≤ 1/2 := by
    have heq : ‖c • a‖ = |inner ℝ a w|/‖a‖ := by
      simp only [norm_smul,Real.norm_eq_abs,c,abs_div,abs_pow,abs_norm]
      field_simp
    rw [heq]
    exact (div_le_iff₀ han).mpr (by linarith)
  have hv : 1/2 ≤ ‖v‖ := by
    have hh : ‖w‖ ≤ ‖v‖ + ‖c • a‖ := by
      simpa only [v,sub_add_cancel] using norm_add_le (w-c • a) (c • a)
    rw [hw] at hh
    linarith
  have hRv : R v = 0 := by simp [v,hRw,hRa]
  have hTv : T v = T w := by simp [v,hTa]
  refine ⟨w,hw,hAw',hRw,?_⟩
  have hh := hco v hav
  rw [hRv,hTv,zero_pow (by norm_num : 2 ≠ 0),zero_add,Real.sqrt_sq_eq_abs] at hh
  linarith

end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem radial_leading_trace (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2) (hrn : ‖r‖ ≤ 2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2))
    (L A δ f b K f₂ : ℝ) (hL : 0 ≤ L) (_hA : 0 ≤ A) (hAL : A ≤ 3*L)
    (hδ : 0 ≤ δ) (hf : 0 ≤ f) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (h₂ : |f₂| ≤ K) (hq : 0 ≤ q) (hqA : q ≤ δ*A*f) :
    ∃ v : E, ‖v‖ = L ∧ inner ℝ (a+q • r+e) v = 0 ∧ R v = 0 ∧
      L^2/16*b - 288*K*δ^2*L^2*f^2 - 8*K*‖e‖^2 ≤
        f₂*(R (a+q • r+e))^2+b*(T (a+q • r+e))^2+
        f₂*(R v)^2+b*(T v)^2 := by
  obtain ⟨w,hw,haw,hRw,hTw⟩ := radial_angular_witness hd a r e ha q R T
    hr hRa hTa he hco
  have hrr : R r = ‖r‖^2 := by rw [←hr,real_inner_self_eq_norm_sq]
  have hRe : |R e| ≤ 2*‖e‖ := by
    rw [←hr]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hrn (norm_nonneg _))
  have hRsum : R (a+q • r+e) = q*‖r‖^2+R e := by simp [map_add,map_smul,hRa,hrr]
  have hRabs : |R (a+q • r+e)| ≤ 4*δ*A*f+2*‖e‖ := by
    rw [hRsum]
    have hh := abs_add_le (q*‖r‖^2) (R e)
    rw [abs_of_nonneg (mul_nonneg hq (sq_nonneg _))] at hh
    have hr2 : ‖r‖^2 ≤ 4 := by nlinarith [norm_nonneg r]
    have hq4 := mul_le_mul_of_nonneg_left hr2 hq
    nlinarith
  have hRL : |R (a+q • r+e)| ≤ 12*δ*L*f+2*‖e‖ := by
    have hh := mul_le_mul_of_nonneg_left hAL (show 0 ≤ 4*δ*f by positivity)
    nlinarith
  have hRsq : (R (a+q • r+e))^2 ≤ 288*δ^2*L^2*f^2+8*‖e‖^2 := by
    have hn : 0 ≤ 12*δ*L*f+2*‖e‖ := by positivity
    have hh := sq_le_sq₀ (abs_nonneg _) hn |>.mpr hRL
    rw [sq_abs] at hh
    nlinarith [sq_nonneg (12*δ*L*f-2*‖e‖)]
  have hf₂ : -K ≤ f₂ := by linarith [neg_abs_le f₂]
  have hlow := mul_le_mul_of_nonneg_right hf₂ (sq_nonneg (R (a+q • r+e)))
  have hKbound := mul_le_mul_of_nonneg_left hRsq hK
  have hwT : (1/16:ℝ) ≤ (T w)^2 := by nlinarith [sq_abs (T w)]
  have hsT : L^2/16 ≤ (T (L • w))^2 := by
    simp only [map_smul,smul_eq_mul,mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hwT (sq_nonneg L)]
  have hbT := mul_le_mul_of_nonneg_left hsT hb
  simp only [map_smul,smul_eq_mul,mul_pow] at hbT
  refine ⟨L • w, ?_, ?_, ?_, ?_⟩
  · simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg hL,hw]
  · simp [inner_smul_right,haw]
  · simp [hRw]
  · simp only [map_smul,smul_eq_mul,hRw,mul_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero]
    nlinarith only [hlow,hKbound,hbT,mul_nonneg hb (sq_nonneg (T (a+q • r+e)))]


end YauCounterexamples
end

end OAI
