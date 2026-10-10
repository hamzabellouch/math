import OAI.Probability.SLE.Geometry.SmallLoopCrossing
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

namespace OAI

/-! A transverse crossing of two smooth planar curves is a locally
injective zero of their two-parameter difference map. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma exists_injective_closedBall_of_strict_deriv {f : ℂ → ℂ} {a : ℂ}
    {L : ℂ →L[ℝ] ℂ} (h : HasStrictFDerivAt f L a) (hi : Injective L) :
    ∃ r : ℝ, 0<r ∧ InjOn f (closedBall a r) := by
  let e : ℂ ≃L[ℝ] ℂ := (LinearEquiv.ofBijective L.toLinearMap
    ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  have he : (e : ℂ →L[ℝ] ℂ)=L := by ext z; rfl
  have h' : HasStrictFDerivAt f (e : ℂ →L[ℝ] ℂ) a := by rwa [he]
  let g := h'.toOpenPartialHomeomorph f
  have ha : a∈g.source := h'.mem_toOpenPartialHomeomorph_source
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (g.open_source.mem_nhds ha)
  refine ⟨r/2,half_pos hr,g.injOn.mono ?_⟩
  exact (closedBall_subset_ball (half_lt_self hr)).trans hball

lemma transverse_difference_locally_injective {c p : ℝ → ℂ} {s t : ℝ} {α β : ℂ}
    (hc : HasStrictDerivAt c α t) (hp : HasStrictDerivAt p β s)
    (htrans : ∀ u v : ℝ, u • α-v • β=0 → u=0 ∧ v=0) :
    ∃ r : ℝ, 0<r ∧ InjOn (fun z : ℂ => c z.im-p z.re)
      (closedBall ((s:ℂ)+(t:ℂ)*Complex.I) r) := by
  let L : ℂ →L[ℝ] ℂ := Complex.imCLM.smulRight α-Complex.reCLM.smulRight β
  have hc' : HasStrictFDerivAt (fun z : ℂ => c z.im)
      (Complex.imCLM.smulRight α) ((s:ℂ)+(t:ℂ)*Complex.I) := by
    have hcbase : HasStrictDerivAt c α (((s:ℂ)+(t:ℂ)*Complex.I).im) := by simpa using hc
    have hcomp : (ContinuousLinearMap.toSpanSingleton ℝ α).comp Complex.imCLM=
        Complex.imCLM.smulRight α := by ext z; rfl
    simpa only [hcomp] using
      hcbase.hasStrictFDerivAt.comp ((s:ℂ)+(t:ℂ)*Complex.I) Complex.imCLM.hasStrictFDerivAt
  have hp' : HasStrictFDerivAt (fun z : ℂ => p z.re)
      (Complex.reCLM.smulRight β) ((s:ℂ)+(t:ℂ)*Complex.I) := by
    have hpbase : HasStrictDerivAt p β (((s:ℂ)+(t:ℂ)*Complex.I).re) := by simpa using hp
    have hcomp : (ContinuousLinearMap.toSpanSingleton ℝ β).comp Complex.reCLM=
        Complex.reCLM.smulRight β := by ext z; rfl
    simpa only [hcomp] using
      hpbase.hasStrictFDerivAt.comp ((s:ℂ)+(t:ℂ)*Complex.I) Complex.reCLM.hasStrictFDerivAt
  apply exists_injective_closedBall_of_strict_deriv (L := L) (hc'.sub hp')
  intro z w he
  have hz : L (z-w)=0 := by rw [map_sub,he,sub_self]
  have hzw : (z-w).im • α-(z-w).re • β=0 := hz
  obtain ⟨him,hre⟩ := htrans _ _ hzw
  apply Complex.ext
  · exact sub_eq_zero.mp hre
  · exact sub_eq_zero.mp him

lemma transverse_radial_angular (A B : ℝ) (q : ℂ)
    (hA : A≠0) (hB : B≠0) (hq : q≠0) :
    ∀ u v : ℝ, u • ((A:ℂ)*Complex.I*q)-v • ((B:ℂ)*q)=0 → u=0 ∧ v=0 := by
  intro u v he
  have heq : ((u*A:ℝ):ℂ)*Complex.I-((v*B:ℝ):ℂ)=0 := by
    apply (mul_eq_zero.mp (show (((u*A:ℝ):ℂ)*Complex.I-((v*B:ℝ):ℂ))*q=0 by
      calc
        _ = u • ((A:ℂ)*Complex.I*q)-v • ((B:ℂ)*q) := by
          simp only [Complex.real_smul,Complex.ofReal_mul]
          ring
        _ = 0 := he)).resolve_right hq
  have hr := congrArg Complex.re heq
  have hi := congrArg Complex.im heq
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,zero_sub,Complex.zero_re] at hr
  simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,sub_zero,Complex.zero_im] at hi
  exact ⟨(mul_eq_zero.mp hi).resolve_right hA,
    (mul_eq_zero.mp (neg_eq_zero.mp hr)).resolve_right hB⟩

end SLEExactGauge

end

end OAI
