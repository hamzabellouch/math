import OAI.Analysis.KadisonKastler.ResolventLocalRootBounds
import OAI.Analysis.KadisonKastler.ModularThresholdBounds
import OAI.Analysis.KadisonKastler.ModularPositiveOperator
import OAI.Analysis.KadisonKastler.GraphResolventFunctionalCalculus

namespace OAI

/-! # A localized vector gives an approximate modular graph pair

The error depends only on the width of the logarithmic interval. No bound
on its center is needed, and both graph coordinates approximate the same
original vector after their separate positive scalar normalizations.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_scaled_error {a ε : ℝ} (ha : 0 < a) (v x : H)
    (h : ‖v-(a : ℂ) • x‖ ≤ ε*a*‖x‖) :
    ‖((a : ℂ)⁻¹) • v-x‖ ≤ ε*‖x‖ := by
  have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have he : ((a : ℂ)⁻¹) • v-x = ((a : ℂ)⁻¹) • (v-(a : ℂ) • x) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hane, one_smul]
  rw [he, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  calc
    _ ≤ a⁻¹*(ε*a*‖x‖) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha.le)
    _ = ε*‖x‖ := by field_simp

variable {M : VonNeumannAlgebra H}

theorem modular_localized_graph_pair
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (ξ : H) {r δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : modularUpperCut M J Ω r ξ=ξ)
    (hhi : modularUpperCut M J Ω (r+δ) ξ=0) :
    ∃ (x y : H) (q : ℝ), 0 < q ∧
      (x,(q : ℂ) • y) ∈ (modularPositiveOperator J Ω hsep hcyc).graph ∧
      ‖x-ξ‖ ≤ (Real.exp δ-1)*‖ξ‖ ∧ ‖y-ξ‖ ≤ (Real.exp δ-1)*‖ξ‖ := by
  let R := graphResolvent M J Ω 1
  let t := modularCutThreshold r
  let a := Real.sqrt t
  let b := Real.sqrt (1-t)
  have ht : 0 < t := modularCutThreshold_pos r
  have ht1 : t < 1 := modularCutThreshold_lt_one r
  have ha : 0 < a := Real.sqrt_pos.mpr ht
  have hb : 0 < b := Real.sqrt_pos.mpr (sub_pos.mpr ht1)
  have hε : 0 ≤ Real.exp δ-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hδ)
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  have hRpos : 0 ≤ R := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (graphResolvent_positive J Ω 1)
  have hRcomp : 0 ≤ 1-R := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    have hs := (tomitaGraphComplementRoot_nonneg (M := M) J Ω).isSelfAdjoint.star_eq
    simpa only [hs] using star_mul_self_nonneg (tomitaGraphComplementRoot (M := M) J Ω)
  have hroot : ‖tomitaGraphRoot (M := M) J Ω ξ-(a : ℂ) • ξ‖ ≤
      (Real.exp δ-1)*a*‖ξ‖ := by
    apply resolventSqrt_local_error R hR hRpos ξ
      (modularCutThreshold (r+δ)) t hhi hlo ht hε
    intro s hs hu
    exact (modularCutThreshold_relative_width hδ hs hu.le).1
  have hcomp : ‖tomitaGraphComplementRoot (M := M) J Ω ξ-(b : ℂ) • ξ‖ ≤
      (Real.exp δ-1)*b*‖ξ‖ := by
    apply resolventComplementSqrt_local_error R hR hRcomp ξ
      (modularCutThreshold (r+δ)) t hhi hlo ht1 hε
      (fun s => (graphResolvent_spectrum_bounds J Ω s.property).2)
    intro s hs hu
    exact (modularCutThreshold_relative_width hδ hs hu.le).2
  refine ⟨((a : ℂ)⁻¹) • tomitaGraphRoot (M := M) J Ω ξ,
    ((b : ℂ)⁻¹) • tomitaGraphComplementRoot (M := M) J Ω ξ,
    b/a, div_pos hb ha, ?_, norm_scaled_error ha _ ξ hroot, norm_scaled_error hb _ ξ hcomp⟩
  apply (modularPositiveOperator_graph_iff J Ω hsep hcyc _ _).mpr
  refine ⟨((a : ℂ)⁻¹) • ξ, ?_, ?_⟩
  · rw [map_smul]
  · rw [map_smul, smul_smul]
    congr 1
    rw [Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne', Complex.ofReal_ne_zero.mpr hb.ne']

end

end KadisonKastler

end OAI
