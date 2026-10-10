import OAI.Analysis.CircleDomains.Topology.JordanLocalSides
import OAI.Analysis.CircleDomains.Selection.RegularContours

namespace OAI

/-! The two halves of an actual scalar-level chart lie on opposite sides
of a Jordan boundary contained in that level. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma level_chart_jordan_sides
    (H : ℂ ≃ₜ ℂ) (f : ℂ → ℝ) (t : ℝ)
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ)) (he : ∀ w, (e w).1 = f w)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t})
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H)) (hxe : x ∈ e.source)
    {r : ℝ} (hr : 0 < r)
    (hbox : Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) ⊆ e.target) :
    (e.symm '' (Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆ jordanInterior H ∧
      e.symm '' (Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆
        (closure (jordanInterior H))ᶜ) ∨
    (e.symm '' (Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆ jordanInterior H ∧
      e.symm '' (Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)) ⊆
        (closure (jordanInterior H))ᶜ) := by
  let B := Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  let P := Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  let M := Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  have hPB : P ⊆ B := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], hq.1.2⟩, hq.2⟩
  have hMB : M ⊆ B := by
    intro q hq
    exact ⟨⟨hq.1.1, by linarith [hq.1.2]⟩, hq.2⟩
  have hx1 : (e x).1 = t := (he x).trans (hlevel hx)
  have hxB : e x ∈ B := by
    exact ⟨⟨by rw [hx1]; linarith, by rw [hx1]; linarith⟩,
      ⟨by linarith, by linarith⟩⟩
  have hN : IsOpen (e.symm '' B) :=
    e.symm.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hbox
  have hSP : IsPreconnected (e.symm '' P) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e.symm
      (e.continuousOn_symm.mono (hPB.trans hbox))
  have hSM : IsPreconnected (e.symm '' M) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e.symm
      (e.continuousOn_symm.mono (hMB.trans hbox))
  have hPf : Disjoint (e.symm '' P) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q, hq, rfl⟩ hqf
    have hcoord : q.1 = t := by
      rw [← e.right_inv (hbox (hPB hq)), he]
      exact hlevel hqf
    linarith [hq.1.1]
  have hMf : Disjoint (e.symm '' M) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q, hq, rfl⟩ hqf
    have hcoord : q.1 = t := by
      rw [← e.right_inv (hbox (hMB hq)), he]
      exact hlevel hqf
    linarith [hq.1.2]
  have hcover : e.symm '' B ⊆ closure ((e.symm '' P) ∪ (e.symm '' M)) := by
    rintro _ ⟨q, hq, rfl⟩
    have hcont := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (hbox hq))
    rcases le_total t q.1 with hqpos | hqneg
    · apply closure_mono subset_union_left
      apply mem_closure_image hcont
      change q ∈ closure (Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r))
      rw [closure_prod_eq, closure_Ioo (by linarith : t ≠ t+r),
        closure_Ioo (by linarith : (e x).2-r ≠ (e x).2+r)]
      exact ⟨⟨hqpos, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
    · apply closure_mono subset_union_right
      apply mem_closure_image hcont
      change q ∈ closure (Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r))
      rw [closure_prod_eq, closure_Ioo (by linarith : t-r ≠ t),
        closure_Ioo (by linarith : (e x).2-r ≠ (e x).2+r)]
      exact ⟨⟨hq.1.1.le, hqneg⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  exact jordan_local_sides H hN ⟨e x, hxB, e.left_inv hxe⟩ hx hSP hSM hPf hMf hcover

end CircleDomainRigidity

end

end OAI
