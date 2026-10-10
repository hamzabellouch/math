import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Straight
import OAI.Geometry.Cannon.PlanarGraphs.GraphShear

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

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPlanarCorner

theorem tame_graph_flat_chart {ι : Type*} [Finite ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    (i : ι) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ F i t∈W ∧
      H (0,0)=F i t ∧ ∀ z∈W,
        (z∈⋃ j, range (F j) ↔ z∈H '' horizontal) := by
  obtain ⟨p,q,hpt,htq,hleft,hright,hcorner⟩ := tame_interior_corner Q (F i) (hQ i) ht₀ ht₁
  obtain ⟨W,hW,htW,hiso⟩ := isolate_edge_interior F hF i hpt htq
  let x := F i t
  let u := F i p-x
  let v := F i q-x
  have hu : u≠0 := sub_ne_zero.mpr ((F i).injective.ne hpt.ne)
  have hv : v≠0 := sub_ne_zero.mpr ((F i).injective.ne htq.ne.symm)
  let r := min ‖u‖ ‖v‖
  have hr : 0<r := lt_min (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  obtain ⟨H₀,hH₀,hHr⟩ := straighten_corner hcorner
  let H := H₀.trans (Homeomorph.addLeft x)
  refine ⟨H,W∩ball x r,hW.inter isOpen_ball,⟨htW,mem_ball_self hr⟩,?_,?_⟩
  · simp [H,hH₀,x]
  · intro z hz
    rw [hiso z hz.1]
    have he : Icc p q=Icc p t∪Icc t q := by
      ext s
      constructor
      · intro hs
        rcases le_total s t with hst|hts
        · exact Or.inl ⟨hs.1,hst⟩
        · exact Or.inr ⟨hts,hs.2⟩
      · rintro (hs|hs)
        · exact ⟨hs.1,hs.2.trans htq.le⟩
        · exact ⟨hpt.le.trans hs.1,hs.2⟩
    rw [he,image_union,hleft,hright]
    have hHimage : H '' horizontal=(fun w : ℂ => x+w) '' (ray u∪ray v) := by
      change ((fun w : ℂ => x+w) ∘ H₀) '' horizontal=_
      rw [image_comp,hHr]
    rw [hHimage,image_union,mem_union,mem_union]
    have hxU : x+u=F i p := by dsimp [u,x]; abel
    have hxV : x+v=F i q := by dsimp [v,x]; abel
    have hmem (w : ℂ) : z∈(fun b : ℂ => x+b) '' ray w ↔
        ∃ s : ℝ, 0 ≤ s ∧ z = x+s•w := by
      constructor
      · rintro ⟨b,⟨s,hs,hb⟩,hbe⟩
        exact ⟨s,hs,by rw [hb] at hbe; exact hbe.symm⟩
      · rintro ⟨s,hs,rfl⟩
        exact ⟨s•w,⟨s,hs,rfl⟩,rfl⟩
    rw [hmem u,hmem v,local_ray_segment (min_le_left _ _) hz.2,
      local_ray_segment (min_le_right _ _) hz.2,hxU,hxV]
    rw [segment_symm (𝕜:=ℝ) (x:=F i p) (y:=x)]
end CannonEmbeddedArc.Arc

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
