import OAI.Analysis.LipschitzHilbert.Geometry.BinaryFarMass
import OAI.Analysis.LipschitzHilbert.Estimates.PopularGroups

namespace OAI

/-! The far-group energy estimate: the actual selected family, localized
by its representative's popularity projection, has total overlap at most
80 times representative length times reference width. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

theorem group_overlap_bound (F : SelectedFarFamily ι) (B : Rectangle) (v : Plane → Plane)
    (hL : ∀ j ∈ F.members, (F.rectangles j).long ≤ B.long)
    (hproj : ∀ j ∈ F.members,
      (F.refRect.coordinateProjection (B.popularSet v) ∩
        F.refRect.coordinateProjection ((F.rectangles j).popularSet v)).Nonempty) :
    (∑ j ∈ F.members, volume ((F.rectangles j).carrier ∩ F.refRect.carrier)) ≤
      ENNReal.ofReal 80*ENNReal.ofReal B.long*ENNReal.ofReal F.refRect.short := by
  have hB := B.long_pos
  let c := (F.refRect.orthogonalCoordinates B.center).1
  have hsub (j : ι) (hj : j ∈ F.members) :
      (F.rectangles j).carrier ∩ F.refRect.carrier ⊆
        (F.rectangles j).carrier ∩ F.refRect.stripSlab c (8*B.long) := by
    intro x hx
    refine ⟨hx.1,(F.refRect.mem_stripSlab c (8*B.long) x).mpr ⟨?_,?_⟩⟩
    · have hh := F.refRect.projected_group_localization B (F.rectangles j) (hL j hj) (hproj j hj) hx.1
      change |(F.refRect.orthogonalCoordinates x).1-c| ≤ _
      exact hh.trans (by linarith [B.long_pos])
    · exact hx.2.2
  have hm := F.strip_mass_bound c (8*B.long) (by positivity : 0 < 8*B.long)
    (fun j hj => (hL j hj).trans (by linarith [B.long_pos]))
  calc
    _ ≤ stripMass F.rectangles F.members F.refRect c (8*B.long) :=
      Finset.sum_le_sum (fun j hj => measure_mono (hsub j hj))
    _ ≤ 10*volume (F.refRect.stripSlab c (8*B.long)) := hm
    _ = _ := by
      rw [F.refRect.volume_stripSlab,ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring

end LipschitzHilbert.SelectedFarFamily

end

end OAI
