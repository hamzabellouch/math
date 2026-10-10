import OAI.Analysis.CircleDomains.Modulus.RegularJordanNormalBox
import OAI.Analysis.CircleDomains.Modulus.NormalChartJordanSides

namespace OAI

/-! Exact interior halves and the outer boundary of a compact normal box. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma normal_box_boundary_not_image
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    {p : ℝ × ℝ} (hp : p ∈ Icc (t-r,-r) (t+r,r))
    (hedge : p.1 = t-r ∨ p.1 = t+r ∨ p.2 = -r ∨ p.2 = r) :
    e p ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) := by
  rintro ⟨q,hq,heq⟩
  have hqK : q ∈ Icc (t-r,-r) (t+r,r) :=
    ⟨⟨hq.1.1.le,hq.2.1.le⟩,⟨hq.1.2.le,hq.2.2.le⟩⟩
  have heqp : q = p := e.injOn (hK hqK) (hK hp) heq
  subst q
  rcases hedge with h | h | h | h
  · exact (ne_of_gt hq.1.1) h
  · exact (ne_of_lt hq.1.2) h
  · exact (ne_of_gt hq.2.1) h
  · exact (ne_of_lt hq.2.2) h

lemma normal_box_jordan_sides (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0) :
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ) ∨
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ) := by
  have hB : Ioo (t-r) (t+r) ×ˢ Ioo (-r) r ⊆ Icc (t-r,-r) (t+r,r) := by
    rintro p ⟨hp,hq⟩
    exact ⟨⟨hp.1.le,hq.1.le⟩,⟨hp.2.le,hq.2.le⟩⟩
  apply normal_chart_jordan_sides H e (e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r))
    ?_ t r hr (hB.trans hK) (subset_refl _) ?_
  · rintro z ⟨p,hp,rfl⟩
    rw [e.left_inv (hK (hB hp))]
    exact hf p (hB hp)
  · exact (hf (t,0) ⟨⟨by linarith,by linarith⟩,⟨by linarith,hr.le⟩⟩).mpr rfl

lemma normal_box_upper_inter (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ) :
    jordanInterior H ∩ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) =
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) := by
  ext z
  constructor
  · rintro ⟨hz,⟨p,hpB,rfl⟩⟩
    have hpos : 0 < p.2 := by
      by_contra h
      rcases lt_or_eq_of_le (not_lt.mp h) with hneg | hzero
      · exact hn ⟨p,⟨hpB.1,⟨hpB.2.1,hneg⟩⟩,rfl⟩ (subset_closure hz)
      · have hfront := (hf p ⟨⟨hpB.1.1.le,hpB.2.1.le⟩,
            ⟨hpB.1.2.le,hpB.2.2.le⟩⟩).mpr hzero
        exact hfront.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hz)
    exact ⟨p,⟨hpB.1,⟨hpos,hpB.2.2⟩⟩,rfl⟩
  · rintro ⟨p,hpP,rfl⟩
    exact ⟨hp ⟨p,hpP,rfl⟩,p,⟨hpP.1,⟨by linarith [hpP.2.1,hpP.2.2],hpP.2.2⟩⟩,rfl⟩

lemma normal_box_lower_inter (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ) :
    jordanInterior H ∩ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) =
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) := by
  ext z
  constructor
  · rintro ⟨hz,⟨p,hpB,rfl⟩⟩
    have hpos : p.2 < 0 := by
      by_contra h
      rcases lt_or_eq_of_le (not_lt.mp h) with hneg | hzero
      · exact hn ⟨p,⟨hpB.1,⟨hneg,hpB.2.2⟩⟩,rfl⟩ (subset_closure hz)
      · have hfront := (hf p ⟨⟨hpB.1.1.le,hpB.2.1.le⟩,
            ⟨hpB.1.2.le,hpB.2.2.le⟩⟩).mpr hzero.symm
        exact hfront.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hz)
    exact ⟨p,⟨hpB.1,⟨hpB.2.1,hpos⟩⟩,rfl⟩
  · rintro ⟨p,hpP,rfl⟩
    exact ⟨hp ⟨p,hpP,rfl⟩,p,⟨hpP.1,⟨hpP.2.1,by linarith [hpP.2.1,hpP.2.2]⟩⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
