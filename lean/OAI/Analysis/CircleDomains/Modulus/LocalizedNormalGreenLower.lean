import OAI.Analysis.CircleDomains.Modulus.LocalizedNormalGreen

namespace OAI

/-! The inward-right counterpart, with the same unit orientation sign. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma localized_normal_green_lower {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r) (hrsmall : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hj : ∀ p ∈ Icc (t-r,-r) (t+r,r), 0 < planarMapJacobian (fderiv ℝ e p))
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hPs : tsupport P ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r))
    (hQs : tsupport Q ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r)) :
    -planarFormIntegral P Q γ =
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
  have hl (y : ℝ) (hy : y ∈ uIcc (-r) 0) :
      P (curveNormalStrip γ (t-r,y)) = 0 ∧ Q (curveNormalStrip γ (t-r,y)) = 0 := by
    rw [uIcc_of_le (neg_nonpos.mpr hr.le)] at hy
    exact hedge _ ⟨⟨le_rfl,hy.1⟩,⟨by linarith,by linarith [hy.2]⟩⟩ (Or.inl rfl)
  have hright (y : ℝ) (hy : y ∈ uIcc (-r) 0) :
      P (curveNormalStrip γ (t+r,y)) = 0 ∧ Q (curveNormalStrip γ (t+r,y)) = 0 := by
    rw [uIcc_of_le (neg_nonpos.mpr hr.le)] at hy
    exact hedge _ ⟨⟨by linarith,hy.1⟩,⟨le_rfl,by linarith [hy.2]⟩⟩ (Or.inr (Or.inl rfl))
  have ht (x : ℝ) (hx : x ∈ uIcc (t-r) (t+r)) :
      P (curveNormalStrip γ (x,-r)) = 0 ∧ Q (curveNormalStrip γ (x,-r)) = 0 := by
    rw [uIcc_of_le (by linarith : t-r ≤ t+r)] at hx
    exact hedge _ ⟨⟨hx.1,le_rfl⟩,⟨hx.2,by linarith⟩⟩ (Or.inr (Or.inr (Or.inl rfl)))
  have hsub : Icc (t-r,-r) (t+r,0) ⊆ Icc (t-r,-r) (t+r,r) := by
    intro p hp
    exact ⟨hp.1,⟨hp.2.1,by linarith [hp.2.2]⟩⟩
  have hi : InjOn (curveNormalStrip γ) (Icc (t-r,-r) (t+r,0)) := by
    rw [← hfe]
    exact e.injOn.mono (hsub.trans hK)
  have hj' : ∀ p ∈ Icc (t-r,-r) (t+r,0),
      0 ≤ planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) := by
    rw [← hfe]
    exact fun p hp => (hj p (hsub hp)).le
  have him := integral_normal_strip_image_rectangle hγ.smooth (t-r) (t+r) (-r) 0 hi hj'
    (fun z => (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I)
  have harea : (∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) =
      ∫ z in e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0),
        (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    rw [← normal_box_lower_inter H e t r hf hp hn]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (jordanInterior_isOpen H).measurableSet inter_subset_left
    intro z hz'
    exact planar_curl_zero_off_support hPs hQs (fun h => hz'.2 ⟨hz'.1,h⟩)
  rw [planarFormIntegral_localized hγ e t r hr hrsmall he hf hP.continuous hQ.continuous hz]
  rw [harea,hfe,him]
  exact (normal_strip_lower_green hP hQ hγ.smooth (t-r) (t+r) r
    (by linarith) hr.le hl hright ht).symm

end CircleDomainRigidity

end

end OAI
