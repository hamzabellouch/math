import OAI.Analysis.KadisonKastler.PureStateExtension

namespace OAI

/-! # A unit-vector witness for a strict state inequality

A self-adjoint operator cannot have a state value above all its vector
values. The proof uses only the quadratic-form order and positivity of states.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem state_value_le_of_vector_bound
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (c : ℝ)
    (hbound : ∀ ξ, (inner ℂ ξ (T ξ)).re ≤ c*‖ξ‖^2) : (φ T).re ≤ c := by
  let B := (c : ℂ) • (1 : H →L[ℂ] H)-T
  have hc : IsSelfAdjoint (c : ℂ) := by simp [isSelfAdjoint_iff]
  have hB : IsSelfAdjoint B := hc.smul (IsSelfAdjoint.one _ ) |>.sub hT
  have hBs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB
  have hpos : B.IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff' B).mpr
    refine ⟨hB,fun ξ => ?_⟩
    have hr : ((inner ℂ (B ξ) ξ).re : ℂ)=inner ℂ (B ξ) ξ :=
      hBs.coe_re_inner_apply_self ξ
    rw [← hr]
    have he : (inner ℂ (B ξ) ξ).re=c*‖ξ‖^2-(inner ℂ ξ (T ξ)).re := by
      simp only [B,sub_apply,smul_apply,one_apply_eq_self,inner_sub_left,inner_smul_left,
        inner_self_eq_norm_sq_to_K]
      change ((star (c : ℂ))*((‖ξ‖ : ℂ)^2)-inner ℂ (T ξ) ξ).re=_
      rw [← Complex.ofReal_pow]
      simp only [Complex.sub_re,Complex.mul_re,Complex.conj_ofReal,
        Complex.star_def,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact congrArg (fun r : ℝ => c*‖ξ‖^2-r)
        (show (inner ℂ (T ξ) ξ).re=(inner ℂ ξ (T ξ)).re from inner_re_symm (𝕜:=ℂ) (T ξ) ξ)
    rw [he]
    exact_mod_cast (sub_nonneg.mpr (hbound ξ))
  have hp := (positiveOfSquares φ hφ.2).map_nonneg
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hpos)
  have hreal := hp.1
  change 0 ≤ (φ ((c : ℂ) • (1 : H →L[ℂ] H)-T)).re at hreal
  rw [map_sub,map_smul,((isState_iff φ).mp hφ).1,smul_eq_mul,mul_one,
    Complex.sub_re,Complex.ofReal_re] at hreal
  linarith

theorem exists_vector_state_gt
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (φ T).re) :
    ∃ ξ : H, ‖ξ‖=1 ∧ c < (inner ℂ ξ (T ξ)).re := by
  have hex : ∃ ξ : H, c*‖ξ‖^2 < (inner ℂ ξ (T ξ)).re := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hc) (state_value_le_of_vector_bound φ hφ T hT c hn)
  obtain ⟨ξ,hξ⟩ := hex
  have hne : ξ ≠ 0 := by
    intro h
    simp only [h,norm_zero,map_zero,inner_zero_left,Complex.zero_re,mul_zero,zero_pow
      (by decide : (2 : ℕ) ≠ 0),lt_self_iff_false] at hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hne
  refine ⟨(‖ξ‖⁻¹ : ℝ) • ξ,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  · have he : (inner ℂ ((‖ξ‖⁻¹ : ℝ) • ξ) (T ((‖ξ‖⁻¹ : ℝ) • ξ))).re=
        ‖ξ‖⁻¹^2*(inner ℂ ξ (T ξ)).re := by
      change (inner ℂ (((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ)
        (T (((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ))).re=_
      rw [map_smul,inner_smul_left,inner_smul_right]
      change (star ((‖ξ‖⁻¹ : ℝ) : ℂ)*
        (((‖ξ‖⁻¹ : ℝ) : ℂ)*inner ℂ ξ (T ξ))).re=_
      simp only [Complex.star_def,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      ring
    rw [he]
    have hm := mul_lt_mul_of_pos_left hξ (sq_pos_of_pos (inv_pos.mpr hn))
    have hi : ‖ξ‖⁻¹^2*‖ξ‖^2=1 := by rw [← mul_pow,inv_mul_cancel₀ hn.ne']; norm_num
    have heq : ‖ξ‖⁻¹^2*(c*‖ξ‖^2)=c := by
      calc
        _ = c*(‖ξ‖⁻¹^2*‖ξ‖^2) := by ring
        _ = c := by rw [hi,mul_one]
    rwa [heq] at hm

end

end KadisonKastler

end OAI
