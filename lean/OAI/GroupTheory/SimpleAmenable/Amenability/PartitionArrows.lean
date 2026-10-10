import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierCells

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PartitionArrows
open Classical Set

abbrev TrackPolygonPartition (a m : ℕ) := Fin m → FinitePolygonPartition a
abbrev PartitionCell {a m : ℕ} (P : TrackPolygonPartition a m) := Σi : Fin m,↥(P i).cells

noncomputable def partitionCellSet {a m : ℕ} {P : TrackPolygonPartition a m}
    (c : PartitionCell P) : Set (TrackPoint a m) := {x | x.1=c.1 ∧ x.2∈c.2.val.val}

theorem partitionCellSet_nonempty {a m : ℕ} {P : TrackPolygonPartition a m}
    (c : PartitionCell P) : (partitionCellSet c).Nonempty := by
  obtain ⟨p,hp⟩ := (P c.1).nonempty c.2.val c.2.property
  exact ⟨(c.1,p),rfl,hp⟩

theorem partitionCellSet_cover {a m : ℕ} (P : TrackPolygonPartition a m) (x : TrackPoint a m) :
    ∃!c : PartitionCell P,x∈partitionCellSet c := by
  obtain ⟨C,⟨hC,hx⟩,hu⟩ := (P x.1).cover x.2
  refine ⟨⟨x.1,⟨C,hC⟩⟩,⟨rfl,hx⟩,?_⟩
  rintro ⟨i,D,hD⟩ ⟨hi,hxD⟩
  dsimp at hi
  subst i
  have he := hu D ⟨hD,hxD⟩
  subst D
  rfl

theorem partitionCellSet_eq_of_mem {a m : ℕ} {P : TrackPolygonPartition a m}
    {c d : PartitionCell P} {x : TrackPoint a m}
    (hc : x∈partitionCellSet c) (hd : x∈partitionCellSet d) : c=d :=
  (partitionCellSet_cover P x).unique hc hd

def PartitionArrow {a m : ℕ} (P Q : TrackPolygonPartition a m) (g : polygonFullGroup a m) : Prop :=
  ∀c : PartitionCell P,∃d : PartitionCell Q,
    g.val '' partitionCellSet c=partitionCellSet d ∧ ∃u : CutRing×CutRing,
      ∀x∈partitionCellSet c,(g.val x).2.val=x.2.val+(ordinary u.1,ordinary u.2)

namespace PartitionArrow
variable {a m : ℕ} {P Q R : TrackPolygonPartition a m} {g h : polygonFullGroup a m}

theorem one (P : TrackPolygonPartition a m) : PartitionArrow P P 1 := by
  intro c
  refine ⟨c,?_,0,?_⟩
  · exact Set.image_id _
  · intro x _
    change x.2.val=x.2.val+(ordinary (0:CutRing),ordinary (0:CutRing))
    simp only [map_zero]
    exact (add_zero x.2.val).symm

theorem mul (hg : PartitionArrow Q R g) (hh : PartitionArrow P Q h) : PartitionArrow P R (g*h) := by
  intro c
  obtain ⟨d,hd,u,hu⟩ := hh c
  obtain ⟨e,he,v,hv⟩ := hg d
  refine ⟨e,?_,u+v,?_⟩
  · change (g.val ∘ h.val) '' partitionCellSet c=partitionCellSet e
    exact (Set.image_image g.val h.val (partitionCellSet c)).symm.trans (by rw [hd,he])
  · intro x hx
    have hhx : h.val x∈partitionCellSet d := by rw [←hd]; exact ⟨x,hx,rfl⟩
    change (g.val (h.val x)).2.val=x.2.val+_
    rw [hv _ hhx,hu _ hx]
    simp only [Prod.fst_add,Prod.snd_add,map_add,Prod.mk_add_mk,add_assoc]

theorem inv (hg : PartitionArrow P Q g) : PartitionArrow Q P g⁻¹ := by
  intro d
  obtain ⟨y,hy⟩ := partitionCellSet_nonempty d
  obtain ⟨c,hc,-⟩ := partitionCellSet_cover P (g.val.symm y)
  obtain ⟨e,he,u,hu⟩ := hg c
  have hye : y∈partitionCellSet e := by rw [←he]; exact ⟨g.val.symm y,hc,g.val.apply_symm_apply y⟩
  have hde : d=e := partitionCellSet_eq_of_mem hy hye
  subst e
  refine ⟨c,?_, -u,?_⟩
  · rw [←he]
    exact g.val.symm_image_image _
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := (Set.mem_image g.val _ _).mp (he.symm ▸ hx)
    have h := hu w hw
    change (g.val.symm (g.val w)).2.val=(g.val w).2.val+_
    rw [g.val.symm_apply_apply,h]
    simp only [Prod.fst_neg,Prod.snd_neg,map_neg]
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> ring

end PartitionArrow
end PartitionArrows

end SimpleAmenable
end
end

end OAI
