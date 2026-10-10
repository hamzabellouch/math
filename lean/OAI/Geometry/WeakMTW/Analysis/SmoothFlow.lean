import Mathlib
import OAI.Geometry.WeakMTW.Analysis.IntegralEquation

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
namespace SmoothFlow

open Set Filter
open scoped Topology ContDiff unitInterval
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem unique_Icc {f : E → E} (hf : ContDiff ℝ 1 f) {u v : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t)
    (hdv : ∀ t ∈ Icc a b, HasDerivWithinAt v (f (v t)) (Icc a b) t)
    (h0 : u a = v a) : EqOn u v (Icc a b) := by
  let S := u '' Icc a b ∪ v '' Icc a b
  have hS : IsCompact S := (isCompact_Icc.image_of_continuousOn hu).union
    (isCompact_Icc.image_of_continuousOn hv)
  obtain ⟨K, hK⟩ := hf.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hS
  exact ODE_solution_unique_of_mem_Icc_right (fun _ _ => hK) hu
    (fun t ht => (hdu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inl (mem_image_of_mem _ (Ico_subset_Icc_self ht))) hv
    (fun t ht => (hdv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inr (mem_image_of_mem _ (Ico_subset_Icc_self ht))) h0

omit [FiniteDimensional ℝ E] in
theorem normalized_rescale {f : E → E} (hf : ContDiff ℝ ∞ f)
    {T s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {u v : C(I, E)}
    (hdu : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      HasDerivWithinAt (fun r => u (projIcc 0 1 zero_le_one r)) (T • f (u ⟨t, ht⟩))
        (Icc (0 : ℝ) 1) t)
    (hdv : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      HasDerivWithinAt (fun r => v (projIcc 0 1 zero_le_one r)) ((s * T) • f (v ⟨t, ht⟩))
        (Icc (0 : ℝ) 1) t)
    (h0 : u 0 = v 0) : ∀ t : I, u (projIcc 0 1 zero_le_one (s * (t : ℝ))) = v t := by
  have hst : MapsTo (fun t : ℝ => s * t) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨mul_nonneg hs.1 ht.1, (mul_le_of_le_one_left ht.1 hs.2).trans ht.2⟩
  let U : ℝ → E := fun t => u (projIcc 0 1 zero_le_one (s * t))
  let V : ℝ → E := fun t => v (projIcc 0 1 zero_le_one t)
  have hU : Continuous U := u.continuous.comp (continuous_projIcc.comp (continuous_const.mul continuous_id))
  have hV : Continuous V := v.continuous.comp continuous_projIcc
  have hdU : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt U ((s * T) • f (U t)) (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hd := (hdu (s * t) (hst ht)).scomp t ((hasDerivAt_id t).const_mul s).hasDerivWithinAt hst
    simpa [U, Function.comp_def, smul_smul, projIcc_of_mem zero_le_one (hst ht)] using hd
  have hdV : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt V ((s * T) • f (V t)) (Icc (0 : ℝ) 1) t := by
    intro t ht
    simpa [V, projIcc_of_mem zero_le_one ht] using hdv t ht
  have heq := unique_Icc ((hf.of_le (by simp)).const_smul (s * T)) hU.continuousOn hV.continuousOn hdU hdV
    (by simpa [U, V] using h0)
  intro t
  simpa [U, V, projIcc_of_mem zero_le_one (hst t.2), projIcc_of_mem zero_le_one t.2] using heq t.2

theorem endpoint_hasDerivAt_ne_zero {f : E → E} (hf : ContDiff ℝ ∞ f)
    {U : Set (ℝ × E)} {Ψ : ℝ × E → C(I, E)} (hU : IsOpen U)
    (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hsol : ∀ q ∈ U, Ψ q = ContinuousMap.const I q.2 +
      q.1 • SmoothODE.integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ (Ψ q)))
    {T : ℝ} {x : E} (hTx : (T, x) ∈ U) (hT : T ≠ 0) :
    HasDerivAt (fun t => Ψ (t, x) 1) (f (Ψ (T, x) 1)) T := by
  let F : ℝ → E := fun t => Ψ (t, x) 1
  have hFc : ContDiffAt ℝ ∞ F T :=
    ((SmoothODE.contDiffOn_endpoint hΨ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)).comp T
      (contDiffAt_id.prodMk contDiffAt_const)
  have hFd : DifferentiableAt ℝ F T := hFc.differentiableAt (by simp)
  have hdu := fun t ht => SmoothODE.integral_curve_derivative (hsol (T, x) hTx) (t := t) ht
  have heq : (fun s : ℝ => F (s * T)) =ᶠ[𝓝[Icc (0 : ℝ) 1] (1 : ℝ)]
      (fun s => Ψ (T, x) (projIcc 0 1 zero_le_one s)) := by
    have hnear : ∀ᶠ s in 𝓝 (1 : ℝ), (s * T, x) ∈ U := by
      have hc : Continuous (fun s : ℝ => (s * T, x)) := by fun_prop
      exact (hc.tendsto 1).eventually (by simpa using hU.mem_nhds hTx)
    filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with s hs hsx
    have hds := fun t ht => SmoothODE.integral_curve_derivative (hsol (s * T, x) hsx) (t := t) ht
    have hz : Ψ (T, x) 0 = Ψ (s * T, x) 0 :=
      (SmoothODE.integral_curve_initial (hsol _ hTx)).trans
        (SmoothODE.integral_curve_initial (hsol _ hsx)).symm
    simpa [F] using (normalized_rescale hf hs hdu hds hz (1 : I)).symm
  have hdcomp : HasDerivWithinAt (fun s : ℝ => F (s * T)) (T • deriv F T)
      (Icc (0 : ℝ) 1) 1 := by
    convert! (hFd.hasDerivAt.scomp_of_eq 1 ((hasDerivAt_id 1).mul_const T) (by simp)).hasDerivWithinAt using 1
    simp
  have hdright : HasDerivWithinAt (fun s => Ψ (T, x) (projIcc 0 1 zero_le_one s))
      (T • f (F T)) (Icc (0 : ℝ) 1) 1 := by
    simpa [F] using hdu 1 (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hUD : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 1 :=
    uniqueDiffOn_Icc zero_lt_one 1 (by constructor <;> norm_num)
  have hsame : T • deriv F T = T • f (F T) :=
    ((hdcomp.congr_of_eventuallyEq heq.symm (by simp [F])).derivWithin hUD).symm.trans
      (hdright.derivWithin hUD)
  have hderiv : deriv F T = f (F T) := (smul_right_injective E hT) hsame
  simpa only [hderiv] using hFd.hasDerivAt

theorem endpoint_hasDerivAt_zero {f : E → E} (hf : ContDiff ℝ ∞ f)
    {U : Set (ℝ × E)} {Ψ : ℝ × E → C(I, E)} (hU : IsOpen U)
    (hΨ : ContDiffOn ℝ ∞ Ψ U)
    (hsol : ∀ q ∈ U, Ψ q = ContinuousMap.const I q.2 +
      q.1 • SmoothODE.integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ (Ψ q)))
    {x : E} (hx : (0, x) ∈ U) : HasDerivAt (fun t => Ψ (t, x) 1) (f x) 0 := by
  let B : C(I, E) → E := fun u => SmoothODE.integralOperator
    (ContinuousMap.comp ⟨f, hf.continuous⟩ u) 1
  have hB : ContDiff ℝ ∞ B :=
    (ContinuousMap.evalCLM ℝ (1 : I)).contDiff.comp
      (SmoothODE.integralOperator.contDiff.comp (SmoothCurveComposition.contDiff_postcomp hf))
  have hP : ContDiffAt ℝ ∞ (fun t : ℝ => Ψ (t, x)) 0 :=
    ((hΨ (0, x) hx).contDiffAt (hU.mem_nhds hx)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)
  have hdB := ((hB.contDiffAt.comp 0 hP).differentiableAt (by simp)).hasDerivAt
  have hzero : Ψ (0, x) = ContinuousMap.const I x := by simpa using hsol (0, x) hx
  have hBzero : B (Ψ (0, x)) = f x := by
    simp [hzero, B, SmoothODE.integralOperator_apply, ContinuousMap.comp_apply]
  have hd : HasDerivAt (fun t : ℝ => x + t • B (Ψ (t, x))) (f x) 0 := by
    convert! (((hasDerivAt_id 0).smul hdB).const_add x) using 1
    simp [hBzero]
  apply hd.congr_of_eventuallyEq
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), (t, x) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt (hU.mem_nhds hx)
  filter_upwards [hnear] with t ht
  have he := congrArg (fun u : C(I, E) => u 1) (hsol (t, x) ht)
  simpa [B] using he

theorem exists_smooth_flow {f : E → E} (hf : ContDiff ℝ ∞ f) (x₀ : E) :
    ∃ (U : Set (ℝ × E)) (Φ : ℝ × E → E),
      IsOpen U ∧ (0, x₀) ∈ U ∧ ContDiffOn ℝ ∞ Φ U ∧
      (∀ x, (0, x) ∈ U → Φ (0, x) = x) ∧
      ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1 := by
  obtain ⟨U, Ψ, hU, hmem, hΨ, _, hsol⟩ := SmoothODE.exists_smooth_integral_curves hf x₀
  refine ⟨U, fun q => Ψ q 1, hU, hmem, SmoothODE.contDiffOn_endpoint hΨ, ?_, ?_⟩
  · intro x hx
    have hz : Ψ (0, x) = ContinuousMap.const I x := by simpa using hsol (0, x) hx
    simp [hz]
  · intro q hq
    rcases q with ⟨T, x⟩
    by_cases hT : T = 0
    · subst T
      have hz : Ψ (0, x) = ContinuousMap.const I x := by simpa using hsol (0, x) hq
      simpa [hz] using endpoint_hasDerivAt_zero hf hU hΨ hsol hq
    · exact endpoint_hasDerivAt_ne_zero hf hU hΨ hsol hq hT

theorem exists_smooth_local_flow {f : E → E} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {x₀ : E} (hx₀ : x₀ ∈ S) :
    ∃ (U : Set (ℝ × E)) (Φ : ℝ × E → E),
      IsOpen U ∧ (0, x₀) ∈ U ∧ ContDiffOn ℝ ∞ Φ U ∧
      (∀ x, (0, x) ∈ U → Φ (0, x) = x) ∧
      ∀ q ∈ U, Φ q ∈ S ∧ HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1 := by
  obtain ⟨g, hg, hgf⟩ := SmoothODE.exists_smooth_extension hS hf hx₀
  obtain ⟨r, hr, hrg⟩ := Metric.eventually_nhds_iff.mp (hgf.and (hS.mem_nhds hx₀))
  obtain ⟨U, Φ, hU, hmem, hΦ, hzero, hd⟩ := exists_smooth_flow hg x₀
  let W := U ∩ Φ ⁻¹' Metric.ball x₀ r
  have hW : IsOpen W := hΦ.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hWmem : (0, x₀) ∈ W := ⟨hmem, by simpa [hzero x₀ hmem] using hr⟩
  refine ⟨W, Φ, hW, hWmem, hΦ.mono inter_subset_left,
    fun x hx => hzero x hx.1, ?_⟩
  intro q hq
  have hnear := hrg hq.2
  exact ⟨hnear.2, hnear.1 ▸ hd q hq.1⟩

end
end SmoothFlow

open Set Filter InnerProductSpace
open scoped Topology ContDiff

end

end WeakMTWGlobalSupport

end OAI
