import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonTrajectoryStrata
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonObjectRefinement

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonStringNormalization

open Classical CategoryTheory Set
namespace PolygonObject
variable {a n : ℕ}

abbrev TrajectoryLabel (F : RawString a n) := Set.range (trajectoryShift F)
noncomputable instance trajectoryLabel_fintype (F : RawString a n) : Fintype (TrajectoryLabel F) :=
  (trajectoryShift_finite_range F).fintype

noncomputable def trajectoryLabel (F : RawString a n) (x : (F.obj 0).Point) : TrajectoryLabel F :=
  ⟨trajectoryShift F x,⟨x,rfl⟩⟩

theorem trajectoryLabel_fiber_polygon (F : RawString a n) (j : Fin (F.obj 0).tracks)
    (u : TrajectoryLabel F) :
    {z | ∃hz : z∈((F.obj 0).cell j).val,trajectoryLabel F ⟨(j,z),hz⟩=u}∈polygonAlgebra a := by
  simpa only [Subtype.ext_iff,trajectoryLabel] using trajectoryShift_fiber_polygon F j u.val

noncomputable def strandObject (F : RawString a n) : PolygonObject a :=
  refinement (F.obj 0) (trajectoryLabel F) (trajectoryLabel_fiber_polygon F)

noncomputable def strandDrop (F : RawString a n) : strandObject F ⟶ F.obj 0 :=
  refinementArrow (F.obj 0) (trajectoryLabel F) (trajectoryLabel_fiber_polygon F)

noncomputable def strandOffsets (F : RawString a n) (i : Fin (n+1))
    (j : Fin (strandObject F).tracks) : CutRing × CutRing :=
  ((Fintype.equivFin (Fin (F.obj 0).tracks × TrajectoryLabel F)).symm j).2.val i

theorem strandOffsets_spec (F : RawString a n) (i : Fin (n+1)) (x : (strandObject F).Point) :
    pointShift (baseArrow F i) ((strandDrop F).toEquiv x)=strandOffsets F i x.val.1 :=
  congrArg (fun (k : TrajectoryLabel F) => k.val i)
    (refinementArrow_label (F.obj 0) (trajectoryLabel F) (trajectoryLabel_fiber_polygon F) x)

noncomputable def translationString (U : PolygonObject a)
    (d : Fin (n+1) → Fin U.tracks → CutRing × CutRing) : RawString a n where
  obj i := shifted U (d i)
  map {i j} _ := CategoryTheory.inv (shiftArrow U (d i)) ≫ shiftArrow U (d j)
  map_id i := by simp
  map_comp f g := by simp [Category.assoc]

noncomputable def normalizedString (F : RawString a n) : RawString a n :=
  translationString (strandObject F) (strandOffsets F)
noncomputable def normalizationLadder (F : RawString a n) : normalizedString F ⟶ F where
  app i := by
    change shifted (strandObject F) (strandOffsets F i) ⟶ F.obj i
    exact CategoryTheory.inv (shiftArrow (strandObject F) (strandOffsets F i)) ≫
      strandDrop F ≫ baseArrow F i
  naturality i j f := by
    change (CategoryTheory.inv (shiftArrow (strandObject F) (strandOffsets F i)) ≫
      shiftArrow (strandObject F) (strandOffsets F j)) ≫
      (CategoryTheory.inv (shiftArrow (strandObject F) (strandOffsets F j)) ≫
        strandDrop F ≫ baseArrow F j) =
      (CategoryTheory.inv (shiftArrow (strandObject F) (strandOffsets F i)) ≫
        strandDrop F ≫ baseArrow F i) ≫ F.map f
    simp [Category.assoc]

theorem normalizationLadder_positional (F : RawString a n) :
    (ladderProperty a n) (normalizationLadder F) := by
  intro i y
  obtain ⟨x,rfl⟩ := (shiftArrow (strandObject F) (strandOffsets F i)).toEquiv.surjective y
  change ((CategoryTheory.inv (shiftArrow (strandObject F) (strandOffsets F i)) ≫
      strandDrop F ≫ baseArrow F i).toEquiv
        ((shiftArrow (strandObject F) (strandOffsets F i)).toEquiv x)).val.2 = _
  simp only [arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  rw [pointShift_spec,strandOffsets_spec]
  rfl

noncomputable def normalizationIso (F : RawString a n) :
    (⟨normalizedString F⟩ : StringGroupoid a n) ≅ ⟨F⟩ :=
  asIso ⟨normalizationLadder F,normalizationLadder_positional F⟩

theorem exists_finite_strand_normalization (F : RawString a n) :
    ∃ (U : PolygonObject a) (d : Fin (n+1) → Fin U.tracks → CutRing × CutRing),
      Nonempty ((⟨translationString U d⟩ : StringGroupoid a n) ≅ ⟨F⟩) :=
  ⟨strandObject F,strandOffsets F,⟨normalizationIso F⟩⟩

end PolygonObject
end PolygonStringNormalization

open Classical CategoryTheory Set
namespace PolygonObject
variable {a n m : ℕ}

@[simp] theorem trajectoryShift_zero (F : RawString a n) (x : (F.obj 0).Point) :
    trajectoryShift F x 0=0 := by
  change pointShift (baseArrow F 0) x=0
  rw [baseArrow_zero,pointShift_id]

theorem trajectoryShift_reindex (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) (i : Fin (n+1)) :
    trajectoryShift (u⋙F) ((baseArrow F (u.obj 0)).toEquiv x) i =
      trajectoryShift F x (u.obj i)-trajectoryShift F x (u.obj 0) := by
  have he := pointShift_comp (baseArrow F (u.obj 0))
    (F.map (u.map (homOfLE (Fin.zero_le i)))) x
  rw [baseArrow_comp] at he
  exact eq_sub_iff_add_eq.mpr he.symm

noncomputable def increments (F : RawString a n) (x : (F.obj 0).Point) :
    Fin n → CutRing × CutRing := fun i =>
      trajectoryShift F x i.succ - trajectoryShift F x i.castSucc

theorem trajectory_successor (F : RawString a n) (x : (F.obj 0).Point) (i : Fin n) :
    trajectory F x i.succ=translate a (increments F x i) (trajectory F x i.castSucc) := by
  change ((baseArrow F i.succ).toEquiv x).val.2=_
  rw [pointShift_spec]
  change translate a (trajectoryShift F x i.succ) x.val.2 =
    translate a (trajectoryShift F x i.succ-trajectoryShift F x i.castSucc)
      ((baseArrow F i.castSucc).toEquiv x).val.2
  rw [pointShift_spec,←translate_add]
  simp only [trajectoryShift,sub_add_cancel]

theorem increments_reindex (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) (i : Fin n) :
    increments (u⋙F) ((baseArrow F (u.obj 0)).toEquiv x) i =
      trajectoryShift F x (u.obj i.succ)-trajectoryShift F x (u.obj i.castSucc) := by
  unfold increments
  rw [trajectoryShift_reindex,trajectoryShift_reindex]
  abel

theorem increments_reindex_unchanged (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) (i : Fin n) (j : Fin m)
    (hleft : u.obj i.castSucc=j.castSucc) (hright : u.obj i.succ=j.succ) :
    increments (u⋙F) ((baseArrow F (u.obj 0)).toEquiv x) i=increments F x j := by
  rw [increments_reindex,hleft,hright]
  rfl

theorem increments_reindex_compose (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) (i : Fin n) (j k : Fin m)
    (hleft : u.obj i.castSucc=j.castSucc) (hmid : j.succ=k.castSucc)
    (hright : u.obj i.succ=k.succ) :
    increments (u⋙F) ((baseArrow F (u.obj 0)).toEquiv x) i=
      increments F x j+increments F x k := by
  rw [increments_reindex,hleft,hright]
  unfold increments
  rw [hmid]
  abel

theorem increments_reindex_duplicate (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) (i : Fin n)
    (hi : u.obj i.succ=u.obj i.castSucc) :
    increments (u⋙F) ((baseArrow F (u.obj 0)).toEquiv x) i=0 := by
  rw [increments_reindex,hi,sub_self]

theorem reindex_initial_position (F : RawString a m)
    (u : Fin (n+1) ⥤ Fin (m+1)) (x : (F.obj 0).Point) :
    ((baseArrow F (u.obj 0)).toEquiv x).val.2=
      translate a (trajectoryShift F x (u.obj 0)) x.val.2 := pointShift_spec _ _

theorem increments_finite_range (F : RawString a n) : (Set.range (increments F)).Finite := by
  exact (trajectoryShift_finite_range F).image (fun t i => t i.succ-t i.castSucc) |>.subset
    (by rintro _ ⟨x,rfl⟩; exact ⟨trajectoryShift F x,⟨x,rfl⟩,rfl⟩)

theorem increments_fiber_polygon (F : RawString a n) (j : Fin (F.obj 0).tracks)
    (u : Fin n → CutRing × CutRing) :
    {z | ∃hz : z∈((F.obj 0).cell j).val,increments F ⟨(j,z),hz⟩=u}∈polygonAlgebra a := by
  let s := (trajectoryShift_finite_range F).toFinset
  have he : {z | ∃hz : z∈((F.obj 0).cell j).val,increments F ⟨(j,z),hz⟩=u} =
      ⋃t∈s.filter (fun t => (fun i : Fin n => t i.succ-t i.castSucc)=u),
        {z | ∃hz : z∈((F.obj 0).cell j).val,trajectoryShift F ⟨(j,z),hz⟩=t} := by
    ext z
    constructor
    · rintro ⟨hz,hu⟩
      refine Set.mem_iUnion₂.mpr ⟨trajectoryShift F ⟨(j,z),hz⟩,
        Finset.mem_filter.mpr ⟨?_,hu⟩,hz,rfl⟩
      exact (Set.Finite.mem_toFinset _).mpr ⟨_,rfl⟩
    · intro hz
      obtain ⟨t,ht,hzt⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨hz',heq⟩ := hzt
      refine ⟨hz',?_⟩
      change (fun i : Fin n => trajectoryShift F ⟨(j,z),hz'⟩ i.succ-
        trajectoryShift F ⟨(j,z),hz'⟩ i.castSucc)=u
      rw [heq]
      exact (Finset.mem_filter.mp ht).2
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro t _
  exact trajectoryShift_fiber_polygon F j t

theorem ladder_preserves_increments {F G : StringGroupoid a n} (h : F ⟶ G)
    (x : (F.obj.obj 0).Point) :
    increments G.obj ((h.hom.app 0).toEquiv x)=increments F.obj x := by
  unfold increments
  rw [ladder_preserves_trajectoryShift]

def deleteVertex (j : Fin (n+2)) : Fin (n+1) ⥤ Fin (n+2) :=
  (Fin.succAboveOrderEmb j).monotone.functor

noncomputable def stringFace (j : Fin (n+2)) : StringGroupoid a (n+1) ⥤ StringGroupoid a n :=
  stringReindex (deleteVertex j)

end PolygonObject

end SimpleAmenable

end OAI
