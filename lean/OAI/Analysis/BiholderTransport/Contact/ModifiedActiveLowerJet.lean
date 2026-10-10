import Mathlib
import OAI.Analysis.BiholderTransport.Duality.ActualLowerJet

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma active_contact_biconjugate {v : M → ℝ} (hv : Continuous v) {x y : M}
    (hactive : contactGap (cTransform v) v x y=0) :
    cTransform (cTransform v) y=v y ∧
      contactGap (cTransform v) (cTransform (cTransform v)) x y=0 := by
  have hle := cTransform_cTransform_le hv y
  have hlo := cTransform_gap_nonneg (continuous_cTransform hv) y x
  rw [contactGap,cost_symm y x] at hlo
  have hact := hactive
  rw [contactGap] at hact
  have he : cTransform (cTransform v) y=v y := by linarith only [hle,hlo,hact]
  exact ⟨he,by simpa only [contactGap,he] using hactive⟩

lemma WeakMTW.modified_active_lower_jet (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v)
    {t s : ℝ} (ht : 0<t) (hts : t<s) (hs1 : s<1) {x:M}
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0<w j) (hsum : ∑ j,w j=1) (i : ι)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap (cTransform v) v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
    (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
      hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q))) :
    HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
      (w i • ((innerSL ℝ).comp R)) := by
  have hdual : IsCostDualPair (cTransform v) (cTransform (cTransform v)) :=
    ⟨(cTransform_triple hv).symm,rfl⟩
  have H := hmtw.actual_active_lower_jet (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) hdual ht hts hs1 pj w hw hsum i
    hmin (fun j => (active_contact_biconjugate hv (hactive j)).2) hleft hright ha ha0 harep
  apply H.mono
  · simp only [add_zero,(active_contact_biconjugate hv (hactive i)).1]
  · filter_upwards [] with d
    have H := cTransform_cTransform_le hv (riemannianExp x (pj i+d))
    linarith only [H]

end WeakMTWTransport

end

end OAI
