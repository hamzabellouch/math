import OAI.Analysis.CircleDomains.Reflection.RegularJordanBoundaryChart
import OAI.Analysis.CircleDomains.Topology.JordanLocalSides

namespace OAI

/-! The two halves of a normal chart lie on the two different Jordan sides. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma normal_chart_jordan_sides (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (U : Set ℂ)
    (hstraight : ∀ z ∈ U, z ∈ frontier (jordanInterior H) ↔ (e.symm z).2 = 0)
    (t r : ℝ) (hr : 0 < r)
    (hbox : Ioo (t-r) (t+r) ×ˢ Ioo (-r) r ⊆ e.source)
    (hBU : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) ⊆ U)
    (ht : e (t,0) ∈ frontier (jordanInterior H)) :
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ) ∨
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ) := by
  let B := Ioo (t-r) (t+r) ×ˢ Ioo (-r) r
  let P := Ioo (t-r) (t+r) ×ˢ Ioo 0 r
  let M := Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0
  have hPB : P ⊆ B := fun q hq => ⟨hq.1,⟨by linarith [hq.2.1],hq.2.2⟩⟩
  have hMB : M ⊆ B := fun q hq => ⟨hq.1,⟨hq.2.1,by linarith [hq.2.2]⟩⟩
  have hN : IsOpen (e '' B) :=
    e.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hbox
  have hP : IsPreconnected (e '' P) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e
      (e.continuousOn.mono (hPB.trans hbox))
  have hM : IsPreconnected (e '' M) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e
      (e.continuousOn.mono (hMB.trans hbox))
  have hPf : Disjoint (e '' P) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q,hq,rfl⟩ hf
    have he := (hstraight (e q) (hBU ⟨q,hPB hq,rfl⟩)).mp hf
    rw [e.left_inv (hbox (hPB hq))] at he
    linarith [hq.2.1]
  have hMf : Disjoint (e '' M) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q,hq,rfl⟩ hf
    have he := (hstraight (e q) (hBU ⟨q,hMB hq,rfl⟩)).mp hf
    rw [e.left_inv (hbox (hMB hq))] at he
    linarith [hq.2.2]
  have hcover : e '' B ⊆ closure ((e '' P) ∪ (e '' M)) := by
    rintro _ ⟨q,hq,rfl⟩
    have hc := e.continuousOn.continuousAt (e.open_source.mem_nhds (hbox hq))
    rcases le_total 0 q.2 with hpos | hneg
    · apply closure_mono subset_union_left
      apply mem_closure_image hc
      change q ∈ closure (Ioo (t-r) (t+r) ×ˢ Ioo 0 r)
      rw [closure_prod_eq,closure_Ioo (by linarith : t-r ≠ t+r),
        closure_Ioo (by linarith : (0 : ℝ) ≠ r)]
      exact ⟨⟨hq.1.1.le,hq.1.2.le⟩,⟨hpos,hq.2.2.le⟩⟩
    · apply closure_mono subset_union_right
      apply mem_closure_image hc
      change q ∈ closure (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0)
      rw [closure_prod_eq,closure_Ioo (by linarith : t-r ≠ t+r),
        closure_Ioo (by linarith : -r ≠ (0 : ℝ))]
      exact ⟨⟨hq.1.1.le,hq.1.2.le⟩,⟨hq.2.1.le,hneg⟩⟩
  apply jordan_local_sides H hN _ ht hP hM hPf hMf hcover
  exact ⟨(t,0),⟨⟨by linarith,by linarith⟩,⟨by linarith,hr⟩⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
