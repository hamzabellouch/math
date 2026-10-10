import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Region

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonFaceIncidence
open Set Topology Metric

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]
theorem flat_chart_boundary_patch {V W : Set X} {π : V → D} (hπ : Continuous π)
    (H : (ℝ × ℝ) ≃ₜ X) (hW : IsOpen W) (h₀ : H (0,0)∈W)
    (hflat : ∀ z∈W, z∈V ↔ (H.symm z).2≠0)
    {d : D} (hd : d∈incident V π (H (0,0))) :
    ∃ U B : Set X, IsOpen U ∧ H (0,0)∈U ∧ U⊆W ∧
      IsConnected B ∧ B⊆W∩region V π d ∧ U∩Vᶜ⊆closure B := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage H.continuous).mem_nhds h₀)
  let C := openBox r
  let U := H '' C
  have hCU : C⊆H ⁻¹' W := by rw [show C=openBox r from rfl,openBox_eq_ball]; exact hball
  have hUW : U⊆W := by rintro _ ⟨p,hp,rfl⟩; exact hCU hp
  have hU : IsOpen U := H.isOpenMap C (by rw [show C=openBox r from rfl,openBox_eq_ball]; exact isOpen_ball)
  have h₀U : H (0,0)∈U := ⟨(0,0),by rw [show C=openBox r from rfl,openBox_eq_ball]; exact mem_ball_self hr,rfl⟩
  let S : Bool → Set X := fun b => H '' halfBox r b
  have hSc (b : Bool) : IsConnected (S b) :=
    (halfBox_connected hr b).image H H.continuous.continuousOn
  have hcover : U∩V=⋃ b, S b := by
    ext x
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpV⟩
      have hp₂ : p.2≠0 := by simpa using (hflat (H p) (hCU hp)).mp hpV
      rcases lt_or_gt_of_ne hp₂ with hl|hr'
      · exact mem_iUnion.mpr ⟨false,⟨p,⟨hp.1,hp.2.1,hl⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨true,⟨p,⟨hp.1,hr',hp.2.2⟩,rfl⟩⟩
    · intro hx
      obtain ⟨b,p,hp,rfl⟩ := mem_iUnion.mp hx
      have hpC : p∈C := by
        cases b
        · exact ⟨hp.1,hp.2.1,hp.2.2.trans hr⟩
        · exact ⟨hp.1,(neg_neg_of_pos hr).trans hp.2.1,hp.2.2⟩
      refine ⟨⟨p,hpC,rfl⟩,(hflat (H p) (hCU hpC)).mpr ?_⟩
      simp only [H.symm_apply_apply]
      cases b
      · exact hp.2.2.ne
      · exact hp.2.1.ne'
  have hclose (b : Bool) : U∩Vᶜ⊆closure (S b) := by
    rintro x ⟨⟨p,hp,hpx⟩,hxV⟩
    subst x
    have hp₂ : p.2=0 := by
      by_contra h
      apply hxV
      apply (hflat (H p) (hCU hp)).mpr
      simpa using h
    rw [show S b=H '' halfBox r b from rfl,←H.image_closure]
    exact ⟨p,halfBox_closure hr hp hp₂ b,rfl⟩
  obtain ⟨labels,hsub,hlabels⟩ := sector_incidence hU inter_subset_left hπ S hSc hcover hclose
  have hnv : H (0,0)∉V := by
    intro h
    have hh := (hflat _ h₀).mp h
    simp at hh
  have hh := hlabels (H (0,0)) ⟨h₀U,hnv⟩
  obtain ⟨b,hb⟩ := hh ▸ hd
  refine ⟨U,S b,hU,h₀U,hUW,hSc b,?_,hclose b⟩
  intro z hz
  refine ⟨hUW ?_,hb ▸ hsub b hz⟩
  exact (hcover.symm ▸ mem_iUnion_of_mem b hz).1
end CannonFaceIncidence

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
