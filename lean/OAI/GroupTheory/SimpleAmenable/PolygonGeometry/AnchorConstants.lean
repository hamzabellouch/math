import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AxisAnchorFamily
import OAI.GroupTheory.SimpleAmenable.CentralCovers.SectorDifferenceRange

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AnchorConstants
namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

theorem constant_range_prefixGroup (hl : 201 ≤ l) (hln : l ≤ n) :
    B.c.range ≤ A.prefixGroup B hlarge g d := by
  have hh := B.fullGeometricSector_partition_range hlarge (axisWindowPrimitives d l q)
    (fun I _ b hb => B.axisFamilyLaw n g d l hln q I b hb) (wholePolygon a)
    (windowCell a d l q) (windowCell_axis_resolved d l (by omega) q)
    (windowCell_pairwise_disjoint d l hl q) (by
      intro x; constructor
      · intro _; exact windowCell_cover d l hl q x
      · intro _; trivial)
  rw [B.fullGeometricSector_whole] at hh
  have hr : (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))).range = B.c.range := by
    apply le_antisymm
    · rintro x ⟨s,rfl⟩; exact ⟨_,rfl⟩
    rintro x ⟨s,rfl⟩
    obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup (Fin (m+1))) s
    exact ⟨t,by simp only [MonoidHom.comp_apply,ht]⟩
  rw [hr] at hh
  apply hh.trans
  apply iSup_le
  intro i
  change (B.axisSector hlarge n g d l hln q (windowCell a d l q i)).range ≤ _
  rw [← A.anchorCopy_eq_cell B hlarge g d hl hln i]
  exact A.anchor_range_prefixGroup B hlarge g d i

end AxisAnchorFamily
end AnchorConstants

end SimpleAmenable
end
end

end OAI
