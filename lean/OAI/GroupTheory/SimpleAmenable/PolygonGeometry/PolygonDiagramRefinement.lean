import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonTrajectoryStrata
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonObjectRefinement

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonDiagramRefinement

open Classical CategoryTheory Set
namespace PolygonObject
variable {a : ℕ}

theorem chart_target_track {U V : PolygonObject a} (f : U ⟶ V)
    (c : Chart (a:=a) U.tracks V.tracks) (hc : c.Holds f.toEquiv) (x : U.Point)
    (hx : c.Contains x) : (f.toEquiv x).val.1=c.target := by
  obtain ⟨hu,he⟩ := hc x.val.2 hx.2
  have hpoint : (⟨(c.source,x.val.2),hu⟩ : U.Point)=x :=
    Subtype.ext (Prod.ext hx.1.symm rfl)
  rw [hpoint] at he
  exact congrArg Prod.fst he

theorem targetTrack_fiber_polygon {U V : PolygonObject a} (f : U ⟶ V)
    (i : Fin U.tracks) (j : Fin V.tracks) :
    {z | ∃hz : z∈(U.cell i).val,(f.toEquiv ⟨(i,z),hz⟩).val.1=j}∈polygonAlgebra a := by
  obtain ⟨s,hs,hcover⟩ := f.hasTable
  have he : {z | ∃hz : z∈(U.cell i).val,(f.toEquiv ⟨(i,z),hz⟩).val.1=j} =
      ⋃c∈s.filter (fun c => c.source=i ∧ c.target=j),c.domain.val := by
    ext z
    constructor
    · rintro ⟨hz,hj⟩
      obtain ⟨c,hc,hz'⟩ := hcover ⟨(i,z),hz⟩
      exact Set.mem_iUnion₂.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hz'.1.symm,
        (chart_target_track f c (hs c hc) ⟨(i,z),hz⟩ hz').symm.trans hj⟩,hz'.2⟩
    · intro hz
      obtain ⟨c,hcf,hcz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨hcs,hci,hcj⟩ := Finset.mem_filter.mp hcf
      obtain ⟨hz',hf⟩ := hs c hcs z hcz
      subst i
      exact ⟨hz',(chart_target_track f c (hs c hcs) ⟨(c.source,z),hz'⟩ ⟨rfl,hcz⟩).trans hcj⟩
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro c _
  exact c.domain.property

abbrev ArrowLabel {U V : PolygonObject a} (f : U ⟶ V) :=
  Fin V.tracks × Set.range (pointShift f)

noncomputable instance arrowLabel_fintype {U V : PolygonObject a} (f : U ⟶ V) :
    Fintype (ArrowLabel f) := by
  letI := (pointShift_finite_range f).fintype
  exact inferInstance

noncomputable def arrowLabel {U V : PolygonObject a} (f : U ⟶ V) (x : U.Point) :
    ArrowLabel f := ⟨(f.toEquiv x).val.1,⟨pointShift f x,⟨x,rfl⟩⟩⟩

theorem arrowLabel_fiber_polygon {U V : PolygonObject a} (f : U ⟶ V)
    (i : Fin U.tracks) (j : ArrowLabel f) :
    {z | ∃hz : z∈(U.cell i).val,arrowLabel f ⟨(i,z),hz⟩=j}∈polygonAlgebra a := by
  have he : {z | ∃hz : z∈(U.cell i).val,arrowLabel f ⟨(i,z),hz⟩=j} =
      {z | ∃hz : z∈(U.cell i).val,(f.toEquiv ⟨(i,z),hz⟩).val.1=j.1} ∩
      {z | ∃hz : z∈(U.cell i).val,pointShift f ⟨(i,z),hz⟩=j.2.val} := by
    ext z
    constructor
    · rintro ⟨hz,he⟩
      exact ⟨⟨hz,congrArg Prod.fst he⟩,⟨hz,congrArg (fun t => t.2.val) he⟩⟩
    · rintro ⟨⟨hz,ht⟩,⟨hz',hs⟩⟩
      exact ⟨hz,Prod.ext ht (Subtype.ext hs)⟩
  rw [he]
  exact (polygonAlgebra a).inf_mem (targetTrack_fiber_polygon f i j.1)
    (pointShift_fiber_polygon f i j.2.val)

variable {κ : Type} [Fintype κ] {U : PolygonObject a}
    {V : κ → PolygonObject a}

noncomputable def diagramLabel (f : ∀k,U ⟶ V k) (x : U.Point) :
    ∀k,ArrowLabel (f k) := fun k => arrowLabel (f k) x

theorem diagramLabel_fiber_polygon (f : ∀k,U ⟶ V k)
    (i : Fin U.tracks) (j : ∀k,ArrowLabel (f k)) :
    {z | ∃hz : z∈(U.cell i).val,diagramLabel f ⟨(i,z),hz⟩=j}∈polygonAlgebra a := by
  have he : {z | ∃hz : z∈(U.cell i).val,diagramLabel f ⟨(i,z),hz⟩=j} =
      (U.cell i).val ∩ ⋂k : κ,{z | ∃hz : z∈(U.cell i).val,arrowLabel (f k) ⟨(i,z),hz⟩=j k} := by
    ext z
    constructor
    · rintro ⟨hz,he⟩
      exact ⟨hz,Set.mem_iInter.mpr (fun k => ⟨hz,congrFun he k⟩)⟩
    · rintro ⟨hz,he⟩
      refine ⟨hz,?_⟩
      funext k
      exact (Set.mem_iInter.mp he k).choose_spec
  rw [he]
  exact (polygonAlgebra a).inf_mem (U.cell i).property
    (BooleanSubalgebra.iInf_mem (fun k => arrowLabel_fiber_polygon (f k) i (j k)))

theorem exists_common_arrow_refinement (f : ∀k,U ⟶ V k) :
    ∃ (W : PolygonObject a) (h : W ⟶ U), Positional h ∧
      ∃ (t : ∀k,Fin W.tracks → Fin (V k).tracks)
        (d : κ → Fin W.tracks → CutRing × CutRing),
        ∀k x,((h≫f k).toEquiv x).val=
          (t k x.val.1,translate a (d k x.val.1) x.val.2) := by
  let W := refinement U (diagramLabel f) (diagramLabel_fiber_polygon f)
  let h := refinementArrow U (diagramLabel f) (diagramLabel_fiber_polygon f)
  let lab (j : Fin W.tracks) :=
    ((Fintype.equivFin (Fin U.tracks × (∀k,ArrowLabel (f k)))).symm j).2
  refine ⟨W,h,refinementArrow_positional _ _ _,
    (fun k j => (lab j k).1),(fun k j => (lab j k).2.val),?_⟩
  intro k x
  have he := congrFun
    (refinementArrow_label U (diagramLabel f) (diagramLabel_fiber_polygon f) x) k
  apply Prod.ext
  · change ((f k).toEquiv (h.toEquiv x)).val.1 = (lab x.val.1 k).1
    exact congrArg (fun t : ArrowLabel (f k) => t.1) he
  · rw [arrow_comp_apply,pointShift_spec]
    change translate a (pointShift (f k) (h.toEquiv x)) x.val.2 = _
    rw [show pointShift (f k) (h.toEquiv x)=(lab x.val.1 k).2.val from
      congrArg (fun t => t.2.val) he]

end PolygonObject
end PolygonDiagramRefinement

end SimpleAmenable
end
end

end OAI
