import OAI.Analysis.Nuclearity.ProductStateFunctional
import OAI.Analysis.PureInfiniteness.FiniteTensorApproximation
import OAI.Analysis.Nuclearity.TensorExcisionEstimate
import OAI.Analysis.Nuclearity.TensorIdealExcisionCut
import OAI.Analysis.PureInfiniteness.StateCutMass
import OAI.Analysis.PureInfiniteness.FinitePureStateExcision

namespace OAI

/-! The excision part of the elementary-ideal theorem: a product pure
state which detects a kernel element detects a positive elementary kernel
element. The separate nuclear ideal-separation step is not assumed here. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

universe u v
variable {A : Type u} {B : Type v} {D : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

private lemma norm_sandwich_contraction {E : Type*} [NonUnitalCStarAlgebra E]
    (g x : E) (hg : ‖g‖ ≤ 1) : ‖g * x * g‖ ≤ ‖x‖ := by
  calc
    _ ≤ (‖g‖ * ‖x‖) * ‖g‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖x‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hg (norm_nonneg _)) hg (norm_nonneg _) (by positivity)
    _ = ‖x‖ := by ring

theorem pure_product_detects_elementary_kernel
    (q : MinimalTensor A B →⋆ₙₐ[ℂ] D)
    (φ : A →ₚ[ℂ] ℂ) (ψ : B →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hpφ : PureStateExcision.ofPositiveState φ hφ ∈
      (PureStateExcision.realStateCarrier (A := A)).extremePoints ℝ)
    (hpψ : PureStateExcision.ofPositiveState ψ hψ ∈
      (PureStateExcision.realStateCarrier (A := B)).extremePoints ℝ)
    (F : MinimalTensor A B →L[ℂ] ℂ) (hFn : ‖F‖ ≤ 1)
    (hF : ∀ a b, F (minimalElementary a b) = φ a * ψ b)
    (z : MinimalTensor A B) (hz : q z = 0) (hFz : F z ≠ 0) :
    ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q (minimalElementary a b) = 0 ∧
      0 < (φ a).re ∧ 0 < (ψ b).re := by
  classical
  let m := ‖F z‖
  have hm : 0 < m := norm_pos_iff.mpr hFz
  obtain ⟨I, hI, a, b, hw⟩ := exists_finite_tensor_approximation z
    (show 0 < m / 128 by positivity)
  let := hI
  let w := ∑ i : I, minimalElementary (a i) (b i)
  let S := ∑ i : I, (‖b i‖ + ‖a i‖)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  let δ := m / (128 * (S + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδS : δ * S ≤ m / 128 := by
    have hh : δ * (S + 1) = m / 128 := by
      dsimp [δ]
      field_simp
    nlinarith
  obtain ⟨e, he, hen, heφ, hea⟩ := pure_state_finite_excision φ hφ hpφ a
    hδ (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨f, hf, hfn, hfψ, hfb⟩ := pure_state_finite_excision ψ hψ hpψ b
    hδ (show (0 : ℝ) < 1 / 4 by norm_num)
  let g := minimalElementary e f
  let γ := ∑ i : I, φ (a i) * ψ (b i)
  have hγ : γ = F w := by simp only [w, map_sum, hF, γ]
  have hgw : ‖g * w * g - γ • minimalElementary (e * e) (f * f)‖ ≤ δ * S :=
    tensor_excision_sum_error_le e f a b (fun i => φ (a i)) (fun i => ψ (b i)) hen hfn
      (fun i => CurrentMain.state_norm_le φ hφ (a i)) hδ.le
      (fun i => (hea i).le) (fun i => (hfb i).le)
  have hgn : ‖g‖ ≤ 1 := by
    rw [norm_minimalElementary]
    nlinarith [norm_nonneg e, norm_nonneg f]
  have hFzw : ‖F z - F w‖ < m / 128 := by
    rw [← map_sub]
    exact ((F.le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hFn)).trans_lt hw
  have hγlarge : m / 2 < ‖γ‖ := by
    have hh := norm_le_norm_sub_add (F z) (F w)
    rw [← hγ] at hh hFzw
    dsimp [m] at hm ⊢
    linarith
  have hqgw : ‖q (g * w * g)‖ ≤ ‖w - z‖ := by
    have heq : q (g * w * g) = q (g * (w - z) * g) := by
      simp only [map_mul, map_sub, hz, sub_zero]
    rw [heq]
    exact (NonUnitalStarAlgHom.norm_apply_le q _).trans
      (norm_sandwich_contraction g (w - z) hgn)
  have hsmall : ‖γ‖ * ‖q (minimalElementary (e * e) (f * f))‖ < m / 32 := by
    have hbound : ‖q (γ • minimalElementary (e * e) (f * f))‖ ≤
        δ * S + ‖w - z‖ := by
      calc
        _ ≤ ‖q (γ • minimalElementary (e * e) (f * f) - g * w * g)‖ +
              ‖q (g * w * g)‖ := by
          simpa only [map_sub] using
            norm_le_norm_sub_add (q (γ • minimalElementary (e * e) (f * f))) (q (g * w * g))
        _ ≤ δ * S + ‖w - z‖ := add_le_add
          ((NonUnitalStarAlgHom.norm_apply_le q _).trans (by simpa only [norm_sub_rev] using hgw)) hqgw
    rw [map_smul, norm_smul] at hbound
    have hw' : ‖w - z‖ < m / 128 := by simpa only [norm_sub_rev] using hw
    linarith
  have hqsmall : ‖q (minimalElementary (e * e) (f * f))‖ ≤ (1 / 4 : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (q (minimalElementary (e * e) (f * f)))]
  have he2 : 0 ≤ e * e := by simpa only [he.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
  have hf2 : 0 ≤ f * f := by simpa only [hf.isSelfAdjoint.star_eq] using star_mul_self_nonneg f
  refine ⟨MainGap.cut (e * e) (1 / 4), MainGap.cut (f * f) (1 / 4),
    MainGap.cut_nonneg _ _, MainGap.cut_nonneg _ _,
    elementary_cut_mem_kernel q _ _ he2 hf2 (by norm_num) hqsmall, ?_, ?_⟩
  · exact state_square_cut_pos φ hφ e he (by norm_num at heφ ⊢; exact heφ)
  · exact state_square_cut_pos ψ hψ f hf (by norm_num at hfψ ⊢; exact hfψ)

theorem pure_product_vanishes_on_kernel
    (q : MinimalTensor A B →⋆ₙₐ[ℂ] D)
    (φ : A →ₚ[ℂ] ℂ) (ψ : B →ₚ[ℂ] ℂ) (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hpφ : PureStateExcision.ofPositiveState φ hφ ∈
      (PureStateExcision.realStateCarrier (A := A)).extremePoints ℝ)
    (hpψ : PureStateExcision.ofPositiveState ψ hψ ∈
      (PureStateExcision.realStateCarrier (A := B)).extremePoints ℝ)
    (F : MinimalTensor A B →L[ℂ] ℂ) (hFn : ‖F‖ ≤ 1)
    (hF : ∀ a b, F (minimalElementary a b) = φ a * ψ b)
    (hzero : ∀ a b, 0 ≤ a → 0 ≤ b → q (minimalElementary a b) = 0 →
      F (minimalElementary a b) = 0)
    (z : MinimalTensor A B) (hz : q z = 0) : F z = 0 := by
  by_contra hFz
  obtain ⟨a, b, ha, hb, hq, hφa, hψb⟩ :=
    pure_product_detects_elementary_kernel q φ ψ hφ hψ hpφ hpψ F hFn hF z hz hFz
  have he := hzero a b ha hb hq
  rw [hF] at he
  have hφ0 : φ a ≠ 0 := by intro h; simp only [h, Complex.zero_re, lt_self_iff_false] at hφa
  have hψ0 : ψ b ≠ 0 := by intro h; simp only [h, Complex.zero_re, lt_self_iff_false] at hψb
  exact (mul_ne_zero hφ0 hψ0) he

end WeakPureInfiniteness

end

end OAI
