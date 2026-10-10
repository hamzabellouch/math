import OAI.Analysis.CircleDomains.Reflection.PrincipalReflectionDefect

namespace OAI

/-! The actual conjugated smooth reflections converge locally uniformly off
the limiting pole. This follows from both retained principal-map limits. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer

lemma locallyUniform_joint_tendsto {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hl : TendstoLocallyUniformly f g atTop) (hg : Continuous g) (z : ℂ) :
    Tendsto (fun p : ℕ × ℂ => f p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 (g z)) :=
  (hg.continuousAt.tendsto.comp tendsto_snd).congr_uniformity
    (tendstoLocallyUniformly_iff_forall_tendsto.mp hl z)

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

def reflectedLimit (D : AnalyticReflectionData C) (i : I) (z : ℂ) : ℂ :=
  star (D.principal (roundReflectionPlane (D.center i) (D.radius i) (D.principal.symm z)))

lemma reflectedLimit_continuousAt (D : AnalyticReflectionData C) (i : I) {z : ℂ}
    (hz : z≠D.principal (D.center i)) : ContinuousAt (D.reflectedLimit i) z := by
  have hi : D.principal.symm z≠D.center i := by
    intro h
    apply hz
    rw [←h,D.principal.apply_symm_apply]
  exact Complex.continuous_conj.continuousAt.comp (D.principal.continuous.continuousAt.comp
    ((roundReflectionPlane_differentiable hi).continuousAt.comp D.principal.symm.continuous.continuousAt))

lemma reflectedApproximation_tendsto (D : AnalyticReflectionData C) (i : I) :
    TendstoLocallyUniformlyOn (D.reflectedApproximation i) (D.reflectedLimit i) atTop
      ({D.principal (D.center i)}ᶜ) := by
  have hf := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp D.limitData.forward
  have hi := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp D.limitData.inverse
  apply (isOpen_compl_singleton.tendstoLocallyUniformlyOn_iff_forall_tendsto).mpr
  intro z hz
  have hz' : z≠D.principal (D.center i) := hz
  have hzi : D.principal.symm z≠D.center i := by
    intro h
    apply hz'
    rw [←h,D.principal.apply_symm_apply]
  have h₁ := locallyUniform_joint_tendsto hi D.principal.symm.continuous z
  have h₂ := (roundReflectionPlane_differentiable (r:=D.radius i) hzi).continuousAt.tendsto.comp h₁
  have h₃ := (locallyUniform_joint_tendsto hf D.principal.continuous
    (roundReflectionPlane (D.center i) (D.radius i) (D.principal.symm z))).comp
      (tendsto_fst.prodMk h₂)
  have h₄ := Complex.continuous_conj.continuousAt.tendsto.comp h₃
  have h₀ : Tendsto (fun p : ℕ × ℂ => D.reflectedLimit i p.2) (atTop ×ˢ 𝓝 z)
      (𝓝 (D.reflectedLimit i z)) := (D.reflectedLimit_continuousAt i hz').tendsto.comp tendsto_snd
  exact (h₀.prodMk_nhds h₄).mono_right (nhds_le_uniformity _)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
