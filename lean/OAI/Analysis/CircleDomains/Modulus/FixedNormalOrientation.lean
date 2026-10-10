import OAI.Analysis.CircleDomains.Modulus.RegularJordanNormalOrientation
import OAI.Analysis.CircleDomains.Modulus.LocalizedNormalGreenLower

namespace OAI

/-! One sign works in every local boundary chart of the same Jordan
circuit, before any differential form is chosen. -/
open Set Function Metric Bornology
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma normal_box_sides_fixed {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (positive : Bool)
    (hglobal : ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ,
      if positive then
        curveNormalStrip γ (t,ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,-ρ) ∈ (closure (jordanInterior H))ᶜ
      else
        curveNormalStrip γ (t,-ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,ρ) ∈ (closure (jordanInterior H))ᶜ) :
    if positive then
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H ∧
        e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ
    else
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H ∧
        e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ := by
  obtain ⟨δ,hδ,hg⟩ := hglobal
  obtain ⟨ρ,hρ0,hρ⟩ := exists_between (lt_min hr hδ)
  have hρr : ρ < r := hρ.trans_le (min_le_left _ _)
  have hρδ : ρ < δ := hρ.trans_le (min_le_right _ _)
  have hplus : e (t,ρ) ∈ e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) :=
    ⟨(t,ρ),⟨⟨by linarith,by linarith⟩,⟨hρ0,hρr⟩⟩,rfl⟩
  have hminus : e (t,-ρ) ∈ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) :=
    ⟨(t,-ρ),⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩,rfl⟩
  rcases normal_box_jordan_sides H e t r hr hK hf with hleft | hright
  · cases positive
    · have hx := (hg ρ ⟨hρ0,hρδ⟩).2
      exact False.elim (hx (subset_closure (he (t,ρ) ▸ hleft.1 hplus)))
    · exact hleft
  · cases positive
    · exact hright
    · have hx := (hg ρ ⟨hρ0,hρδ⟩).1
      exact False.elim ((he (t,ρ) ▸ hright.2 hplus) (subset_closure hx))

lemma regular_jordan_local_green_sign {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    ∃ ε : ℝ, |ε| = 1 ∧ ∀ t : ℝ, ∃ N : Set ℂ, IsOpen N ∧ γ t ∈ N ∧ IsBounded N ∧
      ∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
        tsupport P ⊆ N → tsupport Q ⊆ N →
        ε * planarFormIntegral P Q γ =
          ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  obtain ⟨positive,hglobal⟩ := regular_jordan_global_normal_side hγ
  refine ⟨if positive then 1 else -1,?_,?_⟩
  · cases positive <;> norm_num
  intro t
  obtain ⟨e,r,hr,hrs,he,hs,hK,hf,hj⟩ := exists_regular_jordan_normal_box hγ t
  let B := Ioo (t-r) (t+r) ×ˢ Ioo (-r) r
  have hBK : B ⊆ Icc (t-r,-r) (t+r,r) := by
    rintro p ⟨hp,hq⟩
    exact ⟨⟨hp.1.le,hq.1.le⟩,⟨hp.2.le,hq.2.le⟩⟩
  have hN : IsOpen (e '' B) :=
    e.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) (hBK.trans hK)
  have ht : γ t ∈ e '' B := by
    refine ⟨(t,0),⟨⟨by linarith,by linarith⟩,⟨by linarith,hr⟩⟩,?_⟩
    simp only [he,curveNormalStrip,zero_smul,add_zero]
  have hb : IsBounded (e '' B) :=
    ((isCompact_Icc.image hs.continuous).isBounded).subset (image_mono hBK)
  have hside := normal_box_sides_fixed e t r hr he hK hf positive (hglobal t)
  refine ⟨e '' B,hN,ht,hb,?_⟩
  intro P Q hP hQ hPs hQs
  cases positive
  · simpa using localized_normal_green_lower hγ e t r hr hrs he hK hf hj
      hside.1 hside.2 hP hQ hPs hQs
  · simpa using localized_normal_green_upper hγ e t r hr hrs he hK hf hj
      hside.1 hside.2 hP hQ hPs hQs

end CircleDomainRigidity

end

end OAI
