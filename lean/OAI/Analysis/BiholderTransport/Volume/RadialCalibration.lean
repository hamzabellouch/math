import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.LocalNormalChart

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivAt_regularized_metric_radius (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v, g u v = g v u) {ζ : ℝ → E} {ζ' : E} {t ε τ : ℝ}
    (hζ : HasDerivAt ζ ζ' t) (hpos : 0 < g (ζ t) (ζ t) + ε) :
    HasDerivAt (fun s => τ * Real.sqrt (g (ζ s) (ζ s) + ε))
      (τ * g (ζ t) ζ' / Real.sqrt (g (ζ t) (ζ t) + ε)) t := by
  have h := (((g.hasFDerivAt.comp_hasDerivAt t hζ).clm_apply hζ).add_const ε
    |>.sqrt (ne_of_gt hpos)).const_mul τ
  convert h using 1 <;> try rfl
  simp only [Function.comp_apply,hsym ζ' (ζ t)]
  ring

lemma radial_calibration_length_lower_bound
    (g : E →L[ℝ] E →L[ℝ] ℝ) (hg : ∀ v : E, 0 ≤ g v v)
    (hsym : ∀ u v, g u v = g v u) {ζ : ℝ → E} {a b τ : ℝ}
    (hab : a ≤ b) (hτ : 0 ≤ τ) (hζ : ContDiffOn ℝ 1 ζ (Icc a b)) (hζa : ζ a = 0)
    (B : ℝ → ℝ) (hB : ∀ t ∈ Ioo a b, 0 ≤ B t)
    (hbound : ∀ t ∈ Ioo a b,
      |τ * g (ζ t) (deriv ζ t)| ≤ Real.sqrt (g (ζ t) (ζ t)) * B t) :
    ENNReal.ofReal (τ * Real.sqrt (g (ζ b) (ζ b))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (B t) := by
  by_cases heq : a = b
  · subst b
    simp only [hζa,map_zero,Real.sqrt_zero,mul_zero,ENNReal.ofReal_zero,zero_le]
  have hεbound : ∀ ε : ℝ, 0 < ε →
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ ≤
        ∫⁻ t in Icc a b, ENNReal.ofReal (B t) := by
    intro ε hε
    let F : ℝ → ℝ := fun t => τ * Real.sqrt (g (ζ t) (ζ t)+ε)
    have hF : ContDiffOn ℝ 1 F (Icc a b) :=
      contDiffOn_const.mul (((g.contDiff.comp_contDiffOn hζ).clm_apply hζ).add
        contDiffOn_const |>.sqrt (fun t _ => ne_of_gt (by change 0 < g (ζ t) (ζ t) + ε; linarith [hg (ζ t)])))
    have hlen := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF hab
    have hFa : F a = τ * Real.sqrt ε := by simp only [F,hζa,map_zero,zero_add]
    rw [hFa] at hlen
    apply hlen.trans
    rw [←restrict_Ioo_eq_restrict_Icc]
    apply setLIntegral_mono' measurableSet_Ioo
    intro t ht
    have hζt : HasDerivAt ζ (deriv ζ t) t :=
      ((hζ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero).hasDerivAt
    have hFt := hasDerivAt_regularized_metric_radius g hsym hζt
      (τ := τ) (ε := ε) (by linarith [hg (ζ t)])
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),hFt.deriv,
      Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    have hs : 0 < Real.sqrt (g (ζ t) (ζ t)+ε) := Real.sqrt_pos.2 (by linarith [hg (ζ t)])
    rw [abs_div,abs_of_pos hs,div_le_iff₀ hs]
    refine (hbound t ht).trans ?_
    rw [mul_comm (B t)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (hB t ht)
  have hc : Continuous (fun ε : ℝ =>
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ) := by fun_prop
  have hlim : Tendsto (fun ε : ℝ =>
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ) (𝓝[>] 0)
      (𝓝 (‖τ * Real.sqrt (g (ζ b) (ζ b)+(0:ℝ)) - τ * Real.sqrt (0:ℝ)‖ₑ)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hfinal := le_of_tendsto hlim (show ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ ≤
        ∫⁻ t in Icc a b, ENNReal.ofReal (B t) from by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hεbound ε hε)
  simpa only [add_zero,Real.sqrt_zero,mul_zero,sub_zero,
    Real.enorm_of_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))] using hfinal

lemma fderiv_partial_homeomorph_right_inverse
    (e : OpenPartialHomeomorph E E) {y : E} (hy : y ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm y)) (hi : DifferentiableAt ℝ e.symm y) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ E := by
  have h := he.hasFDerivAt.comp y hi.hasFDerivAt
  exact h.unique ((hasFDerivAt_id y).congr_of_eventuallyEq (e.eventually_right_inverse hy))

lemma normal_chart_gauss_dual_bound
    (e : OpenPartialHomeomorph E E) {y : E} (hy : y ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm y)) (hi : DifferentiableAt ℝ e.symm y)
    (g₀ g₁ : E →L[ℝ] E →L[ℝ] ℝ)
    (hg₁ : ∀ v, v ≠ 0 → 0 < g₁ v v) (hsym : ∀ u v, g₁ u v = g₁ v u)
    (V : E) {τ : ℝ}
    (henergy : g₁ V V = g₀ (e.symm y) (e.symm y))
    (hgauss : ∀ w, g₁ V ((fderiv ℝ e (e.symm y)) w) = τ * g₀ (e.symm y) w)
    (u : E) :
    |τ * g₀ (e.symm y) ((fderiv ℝ e.symm y) u)| ≤
      Real.sqrt (g₀ (e.symm y) (e.symm y)) * Real.sqrt (g₁ u u) := by
  have hd := congrArg (fun L : E →L[ℝ] E => L u)
    (fderiv_partial_homeomorph_right_inverse e hy he hi)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hd
  have hG := hgauss ((fderiv ℝ e.symm y) u)
  rw [hd] at hG
  rw [←hG,←henergy]
  exact positive_bilinear_abs_le g₁ hg₁ hsym V u

lemma normal_chart_radial_path_bound
    (e : OpenPartialHomeomorph E E) (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (h0 : (0:E) ∈ e.source)
    (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (hg₀ : ∀ v, 0 ≤ g₀ v v)
    (hsym₀ : ∀ u v, g₀ u v = g₀ v u)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ y ∈ e.target, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ e.target, ∀ u v, g y u v = g y v u)
    (V : E → E) {τ : ℝ} (hτ : 0 ≤ τ)
    (henergy : ∀ y ∈ e.target, g y (V y) (V y) = g₀ (e.symm y) (e.symm y))
    (hgauss : ∀ y ∈ e.target, ∀ w,
      g y (V y) ((fderiv ℝ e (e.symm y)) w) = τ * g₀ (e.symm y) w)
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (himg : MapsTo γ (Icc a b) e.target)
    (ha : γ a = e 0) :
    ENNReal.ofReal (τ * Real.sqrt (g₀ (e.symm (γ b)) (e.symm (γ b)))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (γ t) (deriv γ t) (deriv γ t))) := by
  let ζ : ℝ → E := e.symm ∘ γ
  have hζ : ContDiffOn ℝ 1 ζ (Icc a b) := hi.comp hγ himg
  have hζa : ζ a = 0 := by simp only [ζ,Function.comp_apply,ha,e.left_inv h0]
  apply radial_calibration_length_lower_bound g₀ hg₀ hsym₀ hab hτ hζ hζa _
    (fun _ _ => Real.sqrt_nonneg _) ?_
  intro t ht
  have hmem := himg (Ioo_subset_Icc_self ht)
  have hγd := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  have hid := (hi.contDiffAt (e.open_target.mem_nhds hmem)).differentiableAt one_ne_zero
  have hed := (he.contDiffAt (e.open_source.mem_nhds (e.map_target hmem))).differentiableAt one_ne_zero
  have hζd := hid.hasFDerivAt.comp_hasDerivAt t hγd.hasDerivAt
  change |τ * g₀ (e.symm (γ t)) (deriv ζ t)| ≤ _
  rw [hζd.deriv]
  exact normal_chart_gauss_dual_bound e hmem hed hid g₀ (g (γ t))
    (hg _ hmem) (hsym _ hmem) (V (γ t)) (henergy _ hmem) (hgauss _ hmem) _

end WeakMTWTransport

end

end OAI
