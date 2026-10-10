import OAI.Analysis.CircleDomains.Sobolev.LocalizedJordanIntegral
import OAI.Analysis.CircleDomains.Modulus.NormalBoxImage
import OAI.Analysis.CircleDomains.Modulus.NormalStripImageGreen

namespace OAI

/-! Green's identity for a smooth form supported in one normal chart on
the inward-left side of a regular Jordan circuit. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma planar_curl_zero_off_support {P Q : ℂ → ℝ} {N : Set ℂ}
    (hP : tsupport P ⊆ N) (hQ : tsupport Q ⊆ N) {z : ℂ} (hz : z ∉ N) :
    (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I = 0 := by
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hQ h)),
    fderiv_of_notMem_tsupport ℝ (fun h => hz (hP h))]
  simp

lemma localized_normal_green_upper {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r) (hrsmall : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hj : ∀ p ∈ Icc (t-r,-r) (t+r,r), 0 < planarMapJacobian (fderiv ℝ e p))
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hPs : tsupport P ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r))
    (hQs : tsupport Q ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r)) :
    planarFormIntegral P Q γ =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have hfe : (e : (ℝ × ℝ) → ℂ) = curveNormalStrip γ := funext he
  have hz : ∀ z ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r), P z = 0 ∧ Q z = 0 := by
    intro z hz
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hz (hPs h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz (hQs h))⟩
  have hedge (p : ℝ × ℝ) (hpK : p ∈ Icc (t-r,-r) (t+r,r))
      (hpe : p.1 = t-r ∨ p.1 = t+r ∨ p.2 = -r ∨ p.2 = r) :
      P (curveNormalStrip γ p) = 0 ∧ Q (curveNormalStrip γ p) = 0 := by
    rw [← he]
    exact hz _ (normal_box_boundary_not_image e t r hK hpK hpe)
  have hl (y : ℝ) (hy : y ∈ uIcc 0 r) :
      P (curveNormalStrip γ (t-r,y)) = 0 ∧ Q (curveNormalStrip γ (t-r,y)) = 0 := by
    rw [uIcc_of_le hr.le] at hy
    exact hedge _ ⟨⟨le_rfl,by linarith [hy.1]⟩,⟨by linarith,hy.2⟩⟩ (Or.inl rfl)
  have hright (y : ℝ) (hy : y ∈ uIcc 0 r) :
      P (curveNormalStrip γ (t+r,y)) = 0 ∧ Q (curveNormalStrip γ (t+r,y)) = 0 := by
    rw [uIcc_of_le hr.le] at hy
    exact hedge _ ⟨⟨by linarith,by linarith [hy.1]⟩,⟨le_rfl,hy.2⟩⟩ (Or.inr (Or.inl rfl))
  have ht (x : ℝ) (hx : x ∈ uIcc (t-r) (t+r)) :
      P (curveNormalStrip γ (x,r)) = 0 ∧ Q (curveNormalStrip γ (x,r)) = 0 := by
    rw [uIcc_of_le (by linarith : t-r ≤ t+r)] at hx
    exact hedge _ ⟨⟨hx.1,by linarith⟩,⟨hx.2,le_rfl⟩⟩ (Or.inr (Or.inr (Or.inr rfl)))
  have hsub : Icc (t-r,0) (t+r,r) ⊆ Icc (t-r,-r) (t+r,r) := by
    intro p hp
    exact ⟨⟨hp.1.1,by linarith [hp.1.2]⟩,hp.2⟩
  have hi : InjOn (curveNormalStrip γ) (Icc (t-r,0) (t+r,r)) := by
    rw [← hfe]
    exact e.injOn.mono (hsub.trans hK)
  have hj' : ∀ p ∈ Icc (t-r,0) (t+r,r),
      0 ≤ planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) := by
    rw [← hfe]
    exact fun p hp => (hj p (hsub hp)).le
  have him := integral_normal_strip_image_rectangle hγ.smooth (t-r) (t+r) 0 r hi hj'
    (fun z => (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I)
  have harea : (∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) =
      ∫ z in e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r),
        (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    rw [← normal_box_upper_inter H e t r hf hp hn]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (jordanInterior_isOpen H).measurableSet inter_subset_left
    intro z hz'
    exact planar_curl_zero_off_support hPs hQs (fun h => hz'.2 ⟨hz'.1,h⟩)
  rw [planarFormIntegral_localized hγ e t r hr hrsmall he hf hP.continuous hQ.continuous hz]
  rw [harea,hfe,him]
  exact (normal_strip_upper_green hP hQ hγ.smooth (t-r) (t+r) r
    (by linarith) hr.le hl hright ht).symm

end CircleDomainRigidity

end

end OAI
