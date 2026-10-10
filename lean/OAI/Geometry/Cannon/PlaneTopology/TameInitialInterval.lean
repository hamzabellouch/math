import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Straight
import OAI.Geometry.Cannon.PlanarGraphs.GraphShear
import OAI.Geometry.Cannon.PlanarGraphs.PositiveHalfAxis

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

namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonPlanarCorner

lemma tame_initial_interval (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) :
    ∃ q : I, 0<q ∧ a '' Icc 0 q=segment ℝ (a 0) (a q) := by
  classical
  obtain ⟨P,h₀,h₁,hP⟩ := finite_segment_arc_subdivision Q a ha
  let R := P.filter (0<·)
  have hR : R.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨h₁,zero_lt_one⟩⟩
  let q := R.min' hR
  have hq := Finset.mem_filter.mp (Finset.min'_mem R hR)
  have hcon : Consecutive P 0 q := by
    refine ⟨h₀,hq.1,hq.2,?_⟩
    intro z hz hz₀ hzq
    exact hzq.not_ge (Finset.min'_le R z (Finset.mem_filter.mpr ⟨hz,hz₀⟩))
  have hh := hP ⟨(0,q),(mem_segments P 0 q).mpr hcon⟩
  rw [subdivArc_range_eq] at hh
  exact ⟨q,hq.2,hh⟩

theorem tame_tip_chart (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) :
    ∃ (H : (ℝ × ℝ) ≃ₜ ℂ) (W : Set ℂ), IsOpen W ∧ a 0∈W ∧ H (0,0)=a 0 ∧
      ∀ z∈W, (z∈range a ↔ z∈H '' positiveHalfAxis) := by
  obtain ⟨q,hq,hseg⟩ := tame_initial_interval a Q ha
  let u := a q-a 0
  have hu : u≠0 := sub_ne_zero.mpr (a.injective.ne hq.ne')
  obtain ⟨H,hH₀,hH⟩ := straight_ray_chart (a 0) u hu
  let T := a '' Ici q
  have hT : IsClosed T := (isClosed_Ici.isCompact.image a.continuous).isClosed
  have hxT : a 0∉T := by
    rintro ⟨s,hs,he⟩
    have he' := a.injective he
    subst s
    exact hq.not_ge hs
  refine ⟨H,Tᶜ∩ball (a 0) ‖u‖,hT.isOpen_compl.inter isOpen_ball,
    ⟨hxT,mem_ball_self (norm_pos_iff.mpr hu)⟩,hH₀,?_⟩
  intro z hz
  rw [hH]
  change (z∈range a ↔ ∃ s : ℝ, 0 ≤ s ∧ z=a 0+s•u)
  rw [local_ray_segment le_rfl hz.2]
  have he : a 0+u=a q := by dsimp [u]; abel
  rw [he,←hseg]
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s,⟨unitInterval.nonneg s,le_of_not_ge (fun hs => hz.1 ⟨s,hs,rfl⟩)⟩,rfl⟩
  · intro hz
    exact image_subset_range _ _ hz

theorem tame_tip_connected_neighborhood (a : Arc ℂ) (Q : Finset (ℂ × ℂ))
    (ha : range a⊆⋃q∈Q, segment ℝ q.1 q.2) {U : Set ℂ} (hU : IsOpen U) (hxU : a 0∈U) :
    ∃ W : Set ℂ, IsOpen W ∧ a 0∈W ∧ W⊆U ∧ IsConnected (W\range a) := by
  obtain ⟨H,W,hW,hxW,h₀,hflat⟩ := tame_tip_chart a Q ha
  have h₀WU : H (0,0)∈W∩U := h₀.symm ▸ ⟨hxW,hxU⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (((hW.inter hU).preimage H.continuous).mem_nhds h₀WU)
  let C := CannonFaceIncidence.openBox r
  let W' := H '' C
  have hsub : C⊆H ⁻¹' (W∩U) := by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact hball
  have hW'U : W'⊆W∩U := by rintro _ ⟨p,hp,rfl⟩; exact hsub hp
  refine ⟨W',H.isOpenMap C (by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact isOpen_ball),
    ⟨(0,0),by rw [show C=CannonFaceIncidence.openBox r from rfl,CannonFaceIncidence.openBox_eq_ball]; exact mem_ball_self hr,h₀⟩,
    fun z hz => (hW'U hz).2,?_⟩
  have he : W'\range a=H '' (C\positiveHalfAxis) := by
    ext z
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpA⟩
      refine ⟨p,⟨hp,?_⟩,rfl⟩
      intro hpR
      exact hpA ((hflat (H p) (hsub hp).1).mpr ⟨p,hpR,rfl⟩)
    · rintro ⟨p,⟨hp,hpR⟩,rfl⟩
      refine ⟨⟨p,hp,rfl⟩,?_⟩
      intro hpA
      obtain ⟨q,hq,heq⟩ := (hflat (H p) (hsub hp).1).mp hpA
      exact hpR (H.injective heq ▸ hq)
  rw [he]
  exact (slit_box_connected hr).image H H.continuous.continuousOn
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
end
end
end
end
end
end

end OAI
