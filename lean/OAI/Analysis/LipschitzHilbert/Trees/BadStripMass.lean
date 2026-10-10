import OAI.Analysis.LipschitzHilbert.Geometry.SelectedFarFamily

namespace OAI

/-! A dense child strip is bounded by its parent's long mass and the
comparable-length estimate. Short members vanish by actual non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert.SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

theorem bad_strip_mass (F : SelectedFarFamily ι) (c l p : ℝ) (hl : 0 < l)
    (hsub : F.refRect.stripSlab c l ⊆ F.refRect.stripSlab p (2*l))
    (hdense : volume (F.refRect.stripSlab c l) ≤
      stripMass F.rectangles (F.longMembers l) F.refRect c l)
    (hparent : stripMass F.rectangles (F.longMembers (2*l)) F.refRect p (2*l) ≤
      4*volume (F.refRect.stripSlab p (2*l))) :
    stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
  let u := F.members.filter (fun j => l ≤ (F.rectangles j).long)
  have hu : stripMass F.rectangles u F.refRect c l =
      stripMass F.rectangles F.members F.refRect c l := by
    apply stripMass_filter_zero
    intro j hj hshort
    have hn := F.short_absent c l hl hdense j hj (lt_of_not_ge hshort)
    have he : (F.rectangles j).carrier ∩ F.refRect.stripSlab c l = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hx
      apply hn
      obtain ⟨x,hxR,hxS⟩ := hx
      exact ⟨x,hxR,stripSlab_mono_length F.refRect c l (4*l) (by linarith) hxS⟩
    rw [he,measure_empty]
  let v := u.filter (fun j => (F.rectangles j).long ≤ 16*l)
  let w := u.filter (fun j => ¬(F.rectangles j).long ≤ 16*l)
  have hv : v ⊆ F.comparableMembers l := by
    intro j hj
    have hju := Finset.mem_filter.mp hj
    have hjs := Finset.mem_filter.mp hju.1
    exact Finset.mem_filter.mpr ⟨hjs.1,hjs.2,hju.2⟩
  have hw : w ⊆ F.longMembers (2*l) := by
    intro j hj
    have hju := Finset.mem_filter.mp hj
    have hjs := Finset.mem_filter.mp hju.1
    apply Finset.mem_filter.mpr
    refine ⟨hjs.1,?_⟩
    linarith
  have hvbound := (stripMass_mono_family F.rectangles v (F.comparableMembers l) hv F.refRect c l).trans
    (F.comparable_mass c l hl)
  have hwbound : stripMass F.rectangles w F.refRect c l ≤
      8*volume (F.refRect.stripSlab c l) := by
    calc
      _ ≤ stripMass F.rectangles (F.longMembers (2*l)) F.refRect c l :=
        stripMass_mono_family F.rectangles w _ hw F.refRect c l
      _ ≤ stripMass F.rectangles (F.longMembers (2*l)) F.refRect p (2*l) :=
        stripMass_mono_region F.rectangles _ F.refRect c l p (2*l) hsub
      _ ≤ 4*volume (F.refRect.stripSlab p (2*l)) := hparent
      _ = _ := by
        rw [stripSlab_volume_parent F.refRect p (2*l) c,show (2*l)/2=l by ring]
        ring
  calc
    _ = stripMass F.rectangles u F.refRect c l := hu.symm
    _ = stripMass F.rectangles v F.refRect c l+stripMass F.rectangles w F.refRect c l :=
      stripMass_filter_partition F.rectangles u F.refRect c l (fun j => (F.rectangles j).long ≤ 16*l)
    _ ≤ 2*volume (F.refRect.stripSlab c l)+8*volume (F.refRect.stripSlab c l) :=
      add_le_add hvbound hwbound
    _ = _ := by ring

end LipschitzHilbert.SelectedFarFamily

end

end OAI
