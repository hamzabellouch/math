import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.JetPullback
import OAI.Analysis.BiholderTransport.Regularity.PrefixAction
import OAI.Analysis.BiholderTransport.Calculus.CompactParameterJets

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitTrialValue_middle_shortLeg {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p∈injectivityDomain x)
    (hF : ContDiffAt ℝ 2 (shortLegCost x t p) 0) :
    splitTrialValue x t 0 k p = t*‖k‖^2+
      fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k/(1-t) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hline : Tendsto (fun r : ℝ => p+r • k) (𝓝 0) (𝓝 p) := by
    simpa only [ContinuousAt,zero_smul,add_zero] using
      (show ContinuousAt (fun r : ℝ => p+r • k) 0 from by fun_prop)
  have he : (fun r : ℝ => splitNormalAction x t p (r • (0:V),p+r • k)) =ᶠ[𝓝 0]
      (fun r : ℝ => t*(‖p+r • k‖^2/2)+shortLegCost x t p (r • k)/(1-t)) := by
    filter_upwards [hline.eventually (prefixAction_axis_near hp)] with r hr
    simp only [splitNormalAction,smul_zero,riemannianExp_zero,shortLegCost]
    have H : cost x (riemannianExp x (t • (p+r • k)))/t=t*(‖p+r • k‖^2/2) := by
      simpa only [prefixAction,riemannianExp_zero] using hr
    rw [H]
  have hnorm : ContDiffAt ℝ 2 (fun v : V => ‖v‖^2/2) p :=
    ((half_norm_sq_contDiff (E := V)).of_le
      (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hnline : ContDiffAt ℝ 2 (fun r : ℝ => ‖p+r • k‖^2/2) 0 := by
    exact (show ContDiffAt ℝ 2 (fun v : V => ‖v‖^2/2) (p+(0:ℝ) • k) from by
      simpa only [zero_smul,add_zero] using hnorm).comp (f := fun r:ℝ => p+r • k) 0 (by fun_prop)
  have hsline : ContDiffAt ℝ 2 (fun r : ℝ => shortLegCost x t p (r • k)) 0 := by
    exact (show ContDiffAt ℝ 2 (shortLegCost x t p) ((0:ℝ) • k) from by
      simpa only [zero_smul] using hF).comp (f := fun r:ℝ => r • k) 0 (by fun_prop)
  rw [splitTrialValue,he.iteratedDeriv_eq 2,
    iteratedDeriv_fun_add (contDiffAt_const.mul hnline) (hsline.div_const (1-t)),
    iteratedDeriv_const_mul t hnline]
  have hN := iteratedDeriv_two_affine_line hnorm k
  rw [half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq] at hN
  have hS := iteratedDeriv_two_affine_line hF k
  simp only [zero_add] at hS
  rw [hN,iteratedDeriv_div_const,hS]

lemma exists_uniform_scaled_middle_bound (R : ℝ) :
    ∃ C>0, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x : M,
      ∀ p k : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R → 0<t → t<1 →
      t • p∈injectivityDomain x → (1-t)*splitTrialValue x t 0 k p ≤ C*‖k‖^2 := by
  obtain ⟨B,HB⟩ := exists_uniform_shortLeg_second_bound (n := n) (M := M) R
  refine ⟨(B:ℝ)+1,by positivity,?_⟩
  filter_upwards [HB] with t ht
  intro x p k hp h0 h1 hpre
  have H := ht x p hp
  rw [splitTrialValue_middle_shortLeg hpre H.1]
  have he : (1-t)*(t*‖k‖^2+
      fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k/(1-t)) =
      (1-t)*t*‖k‖^2+fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k := by
    field_simp [sub_ne_zero.mpr h1.ne']
  rw [he]
  have hB := (le_abs_self (fderiv ℝ (fderiv ℝ (shortLegCost x t p)) 0 k k)).trans
    (by simpa only [Real.norm_eq_abs] using H.2 k)
  have hcoef : (1-t)*t≤1 := by nlinarith
  have Hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖k‖)
  nlinarith

lemma exists_uniform_divided_hessian_gap (R : ℝ) :
    ∃ c>0, ∀ᶠ t in 𝓝 (1:ℝ), ∀ x : M,
      ∀ p xi : TangentSpace 𝓘(ℝ,Model n) x, ‖p‖≤R → 0<t → t<1 →
      p∈injectivityDomain x →
      hessianValue x p xi+c*(1-t)*‖xi‖^2 ≤ hessianValue x (t • p) xi/t := by
  obtain ⟨C,hC,HC⟩ := exists_uniform_scaled_middle_bound (n := n) (M := M) R
  refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
  filter_upwards [HC] with t ht
  intro x p xi hp h0 h1 hpre
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hpre) h0 h1
  by_cases hxi : xi=0
  · subst xi
    simp only [hessianValue_eq_normalHessian hpre,hessianValue_eq_normalHessian hleft,
      map_zero,norm_zero,zero_pow two_ne_zero,mul_zero,add_zero,zero_div,le_refl]
  have hpair : inner ℝ xi xi≠0 := inner_self_ne_zero.mpr hxi
  have hright := shifted_injectivityDomain_of_injectivityDomain hpre h0.le h1
  obtain ⟨hpos,hSchur⟩ := splitTrialValue_schur h0 h1 hpre hleft hright hpair
  rw [splitTrialValue_source,real_inner_self_eq_norm_sq] at hSchur
  have HB := ht x p xi hp h0 h1 hleft
  have Hlower : C⁻¹*(1-t)*‖xi‖^2≤(‖xi‖^2)^2/splitTrialValue x t 0 xi p := by
    apply (le_div_iff₀ hpos).mpr
    have Hmul := mul_le_mul_of_nonneg_right HB (sq_nonneg ‖xi‖)
    have Hdiv := mul_le_mul_of_nonneg_left Hmul (inv_nonneg.mpr hC.le)
    convert! Hdiv using 1 <;> field_simp [hC.ne']
  linarith

end WeakMTWTransport

end

end OAI
