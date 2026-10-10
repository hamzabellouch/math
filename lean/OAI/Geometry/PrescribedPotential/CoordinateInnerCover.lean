import Mathlib
import OAI.Geometry.PrescribedPotential.CoordinateBalls

namespace OAI

/-! Coordinate Inner Cover. -/

section

 

noncomputable section
open Set Metric Filter Topology
namespace Anticanonical.SourceSmooth
open EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace CoordinateBall
variable (p : CoordinateBall A)

def half : CoordinateBall A where
  index := p.index
  center := p.center
  radius := p.radius/2
  radius_pos := by have hp := p.radius_pos; positivity
  closure_sub := (closedBall_subset_closedBall (by linarith [p.radius_pos])).trans p.closure_sub

lemma half_source_sub : p.half.source ⊆ p.source := by
  rintro x ⟨hx,hb⟩
  exact ⟨hx, ball_subset_ball (by change p.radius/2 ≤ p.radius; linarith [p.radius_pos]) hb⟩

lemma centered_small_closedBall_subset {c : EC d} (hc : c ∈ ball p.center (p.radius/2)) :
    closedBall c (p.radius/2) ⊆ ball p.center p.radius := by
  intro z hz
  have hc' : dist c p.center < p.radius/2 := hc
  have hz' : dist z c ≤ p.radius/2 := hz
  change dist z p.center < p.radius
  linarith [dist_triangle z c p.center]

lemma half_exists_at (x : X) : ∃ p : CoordinateBall A, x ∈ p.half.source := by
  obtain ⟨i,hi⟩ := A.covers x
  let e := A.euclideanChart i
  have hs : x ∈ e.source := by simpa [e] using hi
  obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (e.open_target.mem_nhds (e.mapsTo hs))
  refine ⟨⟨i,e x,r/4,by positivity,?_⟩,hs,?_⟩
  · convert hsub using 1; ring_nf
  · exact mem_ball_self (by change 0 < r/4/2; positivity)

theorem finite_inner_cover [CompactSpace X] :
    ∃ S : Finset (CoordinateBall A), ∀ x, ∃ p ∈ S, x ∈ p.half.source := by
  classical
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover
    (fun p : CoordinateBall A => p.half.source) (fun p => p.half.isOpen_source) (by
      intro x _
      obtain ⟨p,hp⟩ := half_exists_at (A := A) x
      exact mem_iUnion.mpr ⟨p,hp⟩)
  refine ⟨S, fun x => ?_⟩
  obtain ⟨p,hp,hx⟩ := mem_iUnion₂.mp (hS (mem_univ x))
  exact ⟨p,hp,hx⟩
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
