import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PeriodicSlotStars
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonStringGroupoid

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonTrajectoryStrata

open Classical CategoryTheory Set
namespace PolygonObject
variable {a n : ℕ}

theorem representative_add (u v : CutRing × CutRing) :
    orbitRepresentative (u+v)=orbitRepresentative u+orbitRepresentative v := by
  simp [orbitRepresentative,add_mul]

@[simp] theorem representative_idem (u : CutRing × CutRing) :
    orbitRepresentative (orbitRepresentative u)=orbitRepresentative u := by
  simp [orbitRepresentative,cutTau]

theorem arrow_displacement_exists {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    ∃u,(f.toEquiv x).val.2=translate a u x.val.2 := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  obtain ⟨c,hc,ht,hx⟩ := hcover x
  obtain ⟨hu,he⟩ := hs c hc x.val.2 hx
  have hpoint : (⟨(c.source,x.val.2),hu⟩ : U.Point)=x :=
    Subtype.ext (Prod.ext ht.symm rfl)
  rw [hpoint] at he
  exact ⟨c.shift,congrArg Prod.snd he⟩

noncomputable def pointShift {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    CutRing × CutRing := orbitRepresentative (arrow_displacement_exists f x).choose

theorem pointShift_spec {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    (f.toEquiv x).val.2=translate a (pointShift f x) x.val.2 :=
  (arrow_displacement_exists f x).choose_spec.trans (translate_orbitRepresentative _ _ _)

theorem pointShift_unique {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point)
    (u : CutRing × CutRing) (he : (f.toEquiv x).val.2=translate a u x.val.2) :
    pointShift f x=orbitRepresentative u :=
  orbitRepresentative_eq_of_translate_eq x.val.2
    ((arrow_displacement_exists f x).choose_spec.symm.trans he)

@[simp] theorem pointShift_reduced {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    orbitRepresentative (pointShift f x)=pointShift f x := representative_idem _

@[simp] theorem pointShift_id (U : PolygonObject a) (x : U.Point) : pointShift (𝟙 U) x=0 := by
  change pointShift (𝟙 U) x=(0,0)
  simpa [orbitRepresentative] using pointShift_unique (𝟙 U) x 0 (by simp [arrow_id_apply])

theorem pointShift_comp {U V W : PolygonObject a} (f : U ⟶ V) (g : V ⟶ W) (x : U.Point) :
    pointShift (f≫g) x=pointShift g (f.toEquiv x)+pointShift f x := by
  have he := pointShift_unique (f≫g) x (pointShift g (f.toEquiv x)+pointShift f x) (by
    rw [arrow_comp_apply,pointShift_spec g,pointShift_spec f,translate_add])
  simpa only [representative_add,pointShift_reduced] using he

theorem chart_pointShift {U V : PolygonObject a} (f : U ⟶ V)
    (c : Chart (a:=a) U.tracks V.tracks) (hc : c.Holds f.toEquiv) (x : U.Point)
    (hx : c.Contains x) : pointShift f x=orbitRepresentative c.shift := by
  obtain ⟨hu,he⟩ := hc x.val.2 hx.2
  have hpoint : (⟨(c.source,x.val.2),hu⟩ : U.Point)=x :=
    Subtype.ext (Prod.ext hx.1.symm rfl)
  rw [hpoint] at he
  exact pointShift_unique f x _ (congrArg Prod.snd he)

theorem pointShift_finite_range {U V : PolygonObject a} (f : U ⟶ V) :
    (Set.range (pointShift f)).Finite := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  apply (s.finite_toSet.image (fun c => orbitRepresentative c.shift)).subset
  rintro _ ⟨x,rfl⟩
  obtain ⟨c,hc,hx⟩ := hcover x
  exact ⟨c,hc,(chart_pointShift f c (hs c hc) x hx).symm⟩

theorem pointShift_fiber_polygon {U V : PolygonObject a} (f : U ⟶ V)
    (i : Fin U.tracks) (u : CutRing × CutRing) :
    {z | ∃hz : z∈(U.cell i).val, pointShift f ⟨(i,z),hz⟩=u}∈polygonAlgebra a := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  have he : {z | ∃hz : z∈(U.cell i).val, pointShift f ⟨(i,z),hz⟩=u} =
      ⋃c∈s.filter (fun c => c.source=i ∧ orbitRepresentative c.shift=u),c.domain.val := by
    ext z
    constructor
    · rintro ⟨hz,hu⟩
      obtain ⟨c,hc,hz'⟩ := hcover ⟨(i,z),hz⟩
      exact Set.mem_iUnion₂.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hz'.1.symm,
        (chart_pointShift f c (hs c hc) ⟨(i,z),hz⟩ hz').symm.trans hu⟩,hz'.2⟩
    · intro hz
      obtain ⟨c,hcf,hcz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨hcs,hci,hcu⟩ := Finset.mem_filter.mp hcf
      obtain ⟨hz',hf⟩ := hs c hcs z hcz
      subst i
      refine ⟨hz',?_⟩
      exact (chart_pointShift f c (hs c hcs) ⟨(c.source,z),hz'⟩ ⟨rfl,hcz⟩).trans hcu
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro c _
  exact c.domain.property

noncomputable def trajectoryShift (F : RawString a n) (x : (F.obj 0).Point) :
    Fin (n+1) → CutRing × CutRing := fun i => pointShift (baseArrow F i) x

theorem trajectoryShift_fiber_polygon (F : RawString a n) (j : Fin (F.obj 0).tracks)
    (u : Fin (n+1) → CutRing × CutRing) :
    {z | ∃hz : z∈((F.obj 0).cell j).val, trajectoryShift F ⟨(j,z),hz⟩=u}∈polygonAlgebra a := by
  have he : {z | ∃hz : z∈((F.obj 0).cell j).val, trajectoryShift F ⟨(j,z),hz⟩=u} =
      ⋂i : Fin (n+1),{z | ∃hz : z∈((F.obj 0).cell j).val,
        pointShift (baseArrow F i) ⟨(j,z),hz⟩=u i} := by
    ext z
    constructor
    · rintro ⟨hz,hu⟩
      exact Set.mem_iInter.mpr (fun i => ⟨hz,congrFun hu i⟩)
    · intro hz
      have h := Set.mem_iInter.mp hz
      obtain ⟨hz',_⟩ := h 0
      refine ⟨hz',?_⟩
      funext i
      exact (h i).choose_spec
  rw [he]
  exact BooleanSubalgebra.iInf_mem (fun i => pointShift_fiber_polygon (baseArrow F i) j (u i))

theorem trajectoryShift_finite_range (F : RawString a n) :
    (Set.range (trajectoryShift F)).Finite := by
  let S (i : Fin (n+1)) := Set.range (pointShift (baseArrow F i))
  let : ∀ index, Finite (S index) := fun index =>
    (pointShift_finite_range (baseArrow F index)).to_subtype
  let val : (∀i,S i) → (Fin (n+1) → CutRing × CutRing) := fun t i => (t i).val
  apply (Set.finite_range val).subset
  rintro _ ⟨x,rfl⟩
  exact ⟨fun i => ⟨pointShift (baseArrow F i) x,⟨x,rfl⟩⟩,rfl⟩

theorem ladder_preserves_trajectoryShift {F G : StringGroupoid a n} (h : F ⟶ G)
    (x : (F.obj.obj 0).Point) :
    trajectoryShift G.obj ((h.hom.app 0).toEquiv x)=trajectoryShift F.obj x := by
  funext i
  have he : translate a (pointShift (baseArrow G.obj i) ((h.hom.app 0).toEquiv x)) x.val.2 =
      translate a (pointShift (baseArrow F.obj i) x) x.val.2 := by
    calc
      _ = translate a (pointShift (baseArrow G.obj i) ((h.hom.app 0).toEquiv x))
          ((h.hom.app 0).toEquiv x).val.2 := congrArg _ (h.property 0 x).symm
      _ = trajectory G.obj ((h.hom.app 0).toEquiv x) i := (pointShift_spec _ _).symm
      _ = trajectory F.obj x i := congrFun (ladder_preserves_trajectory h x) i
      _ = _ := pointShift_spec _ _
  exact (pointShift_reduced _ _).symm.trans
    ((orbitRepresentative_eq_of_translate_eq x.val.2 he).trans (pointShift_reduced _ _))

theorem trajectory_stratification (F : RawString a n) :
    ∃s : Finset (Fin (n+1) → CutRing × CutRing),
      (∀x,trajectoryShift F x∈s) ∧
      (∀j u,{z | ∃hz : z∈((F.obj 0).cell j).val,
        trajectoryShift F ⟨(j,z),hz⟩=u}∈polygonAlgebra a) := by
  refine ⟨(trajectoryShift_finite_range F).toFinset,?_,trajectoryShift_fiber_polygon F⟩
  intro x
  exact (Set.Finite.mem_toFinset _).mpr ⟨x,rfl⟩

end PolygonObject
end PolygonTrajectoryStrata

end SimpleAmenable
end
end

end OAI
