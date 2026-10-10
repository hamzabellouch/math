import Mathlib
import OAI.CategoryTheory.Thomason.CylinderProfiles

namespace OAI

/-! Edge Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.CylinderTables
open Table
variable {M : DirectedComplex.{u}}

lemma crossingProfile_bounded {n : ℕ} (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate (n+1) false t = t) :
    truncate n false (crossingProfile t hs ht) = crossingProfile t hs ht := by
  apply dimension_of_rows_above_zero
  intro p hp b
  exact cross_of_row_zero t p b (row_above_fixed t hb (by omega) b)

lemma leftProfile_bounded {n : ℕ} (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate n false t = t) :
    truncate n false (leftProfile t hs ht) = leftProfile t hs ht := by
  apply dimension_of_rows_above_zero
  intro p hp b
  change leftProfileRow t p b = 0
  have ha := side_of_row_zero t false p b (row_above_fixed t hb hp b)
  have hc := cross_of_row_zero t p b (row_above_fixed t hb (by omega) b)
  simp only [leftProfileRow,ha,hc,ite_self,add_zero]

lemma rightProfile_bounded {n : ℕ} (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1)
    (hb : truncate n false t = t) :
    truncate n false (rightProfile t hs ht) = rightProfile t hs ht := by
  apply dimension_of_rows_above_zero
  intro p hp b
  change rightProfileRow t p b = 0
  have ha := side_of_row_zero t true p b (row_above_fixed t hb hp b)
  have hc := cross_of_row_zero t p b (row_above_fixed t hb (by omega) b)
  simp only [rightProfileRow,ha,hc,ite_self,add_zero]

lemma object_rows_equal (c : Table M) (hc : truncate 0 false c = c) (a b : Bool) :
    c.row 0 a = c.row 0 b := by
  have h (e : Bool) : c.row 0 false = c.row 0 e := by
    simpa only [truncate_top_row] using congrArg (fun x : Table M => x.row 0 e) hc
  exact (h a).symm.trans (h b)

lemma vertical_object_face (c : Table M) (hc : truncate 0 false c = c) (a : Bool) :
    truncate 0 a (verticalTable c) = (M.cylinderEndpoint a).table c := by
  ext p b
  change (truncate 0 a (verticalTable c)).row p b = M.cylinderEndpointMap a p (c.row p b)
  cases p with
  | zero =>
    rw [truncate_top_row]
    change verticalRow c 0 a = M.cylinderEndpointMap a 0 (c.row 0 b)
    cases a <;> simp only [verticalRow,Bool.false_eq_true,ite_false,ite_true,
      object_rows_equal c hc _ b] <;> rfl
  | succ p =>
    rw [truncate_row]
    simp only [show ¬p+1 < 0 by omega,show p+1 ≠ 0 by omega,ite_false,
      row_above_fixed c hc (by omega : 0 < p+1),map_zero]

lemma crossing_edge_left_target (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 true (leftProfile t hs ht) = crossingProfile t hs ht := by
  have hz := (crossing_starts_ends hM t hs ht).2
  have hc := crossingProfile_bounded t hs ht hb
  ext p b
  cases p with
  | zero =>
    rw [truncate_top_row]
    change leftProfileRow t 0 true = (crossingProfile t hs ht).row 0 b
    simp only [leftProfileRow, Even.zero, ite_true, hz, zero_add]
    exact object_rows_equal (crossingProfile t hs ht) hc true b
  | succ p =>
    rw [truncate_row]
    simp only [show ¬p+1 < 0 by omega,show p+1 ≠ 0 by omega,ite_false,
      row_above_fixed _ hc (by omega : 0 < p+1)]

lemma crossing_edge_right_source (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 false (rightProfile t hs ht) = crossingProfile t hs ht := by
  have hz := (crossing_starts_ends hM t hs ht).1
  have hc := crossingProfile_bounded t hs ht hb
  ext p b
  cases p with
  | zero =>
    rw [truncate_top_row]
    change rightProfileRow t 0 false = (crossingProfile t hs ht).row 0 b
    simp only [rightProfileRow, Even.zero, ite_true, Bool.false_eq_true, ite_false, hz, zero_add]
    exact object_rows_equal (crossingProfile t hs ht) hc false b
  | succ p =>
    rw [truncate_row]
    simp only [show ¬p+1 < 0 by omega,show p+1 ≠ 0 by omega,ite_false,
      row_above_fixed _ hc (by omega : 0 < p+1)]

lemma crossing_edge_matching_left (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 true ((M.cylinderEndpoint false).table (leftProfile t hs ht)) =
      truncate 0 false (verticalTable (crossingProfile t hs ht)) := by
  rw [vertical_object_face _ (crossingProfile_bounded t hs ht hb), ← Hom.table_truncate,
    crossing_edge_left_target hM t hs ht hb]

lemma crossing_edge_matching_right (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    truncate 0 true (comp 0 ((M.cylinderEndpoint false).table (leftProfile t hs ht))
      (verticalTable (crossingProfile t hs ht)) (crossing_edge_matching_left hM t hs ht hb)) =
      truncate 0 false ((M.cylinderEndpoint true).table (rightProfile t hs ht)) := by
  rw [target_comp_le 0 0 le_rfl, vertical_object_face _ (crossingProfile_bounded t hs ht hb),
    ← Hom.table_truncate,crossing_edge_right_source hM t hs ht hb]

lemma crossing_edge_factor (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : label t false = 0) (ht : label t true = 1) (hb : truncate 1 false t = t) :
    comp 0 (comp 0 ((M.cylinderEndpoint false).table (leftProfile t hs ht))
      (verticalTable (crossingProfile t hs ht)) (crossing_edge_matching_left hM t hs ht hb))
      ((M.cylinderEndpoint true).table (rightProfile t hs ht))
      (crossing_edge_matching_right hM t hs ht hb) = t := by
  have hc := crossingProfile_bounded t hs ht hb
  have hzc (p : ℕ) (hp : 0 < p) (b : Bool) := row_above_fixed (crossingProfile t hs ht) hc hp b
  obtain ⟨hsrc,htgt⟩ := crossing_starts_ends hM t hs ht
  ext p b
  rw [comp_row,comp_row]
  cases p with
  | zero =>
    cases b
    · change (M.cylinderEndpointMap false 0 ((leftProfile t hs ht).row 0 false)) = t.row 0 false
      change (side t false 0 false + 0,0) = t.row 0 false
      rw [add_zero]
      exact Prod.ext rfl hsrc.symm
    · change (M.cylinderEndpointMap true 0 ((rightProfile t hs ht).row 0 true)) = t.row 0 true
      change (0,side t true 0 true + 0) = t.row 0 true
      rw [add_zero]
      exact Prod.ext htgt.symm rfl
  | succ p =>
    simp only [show ¬p+1 < 0 by omega, show p+1 ≠ 0 by omega, ite_false]
    change M.cylinderEndpointMap false (p+1) (leftProfileRow t (p+1) b) +
      verticalRow (crossingProfile t hs ht) (p+1) b +
      M.cylinderEndpointMap true (p+1) (rightProfileRow t (p+1) b) = t.row (p+1) b
    have hz : cross t (p+1) b = 0 := hzc (p+1) (by omega) b
    have hleft : leftProfileRow t (p+1) b = side t false (p+1) b := by
      simp only [leftProfileRow,hz,ite_self,add_zero]
    have hright : rightProfileRow t (p+1) b = side t true (p+1) b := by
      simp only [rightProfileRow,hz,ite_self,add_zero]
    rw [hleft,hright]
    have hv : verticalRow (crossingProfile t hs ht) (p+1) b = (0,0,cross t p b) := by
      simp only [verticalRow,hzc (p+1) (by omega) b]
      split_ifs <;> rfl
    rw [hv]
    change (side t false (p+1) b,0,0) + (0,0,cross t p b) +
      (0,side t true (p+1) b,0) = t.row (p+1) b
    simp only [Prod.mk_add_mk,add_zero,zero_add]
    rfl
end Thomason.DirectedComplex.CylinderTables

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

variable {X Y : OmegaCategory.{u}} {M : DirectedComplex.{u}}

def verticalObject (c : X.Objects) : (tensorFunctor.obj X).Cell :=
  (generatorCylinder 0 c).map (verticalTable (topTable 0))

lemma verticalObject_bounded (c : X.Objects) :
    (tensorFunctor.obj X).source 1 (verticalObject c) = verticalObject c := by
  change (tensorFunctor.obj X).source 1 ((generatorCylinder 0 c).map _) = _
  erw [← (generatorCylinder 0 c).map_source]
  change (generatorCylinder 0 c).map (truncate 1 false (verticalTable (topTable 0))) = _
  rw [vertical_fixed _ (topTable_bounded 0)]
  rfl

lemma verticalObject_face (c : X.Objects) (a : Bool) :
    (tensorFunctor.obj X).face 0 a (verticalObject c) = ((tensorEndpoint a).app X).map c.val := by
  unfold verticalObject
  erw [← (generatorCylinder 0 c).map_face]
  have he : (K.{u} 0).nu.face 0 a (verticalTable (topTable 0)) = atEnd a (topTable 0) := by
    change (if a then truncate 0 true (verticalTable (topTable 0)) else
      truncate 0 false (verticalTable (topTable 0))) = _
    cases a <;> exact CylinderTables.vertical_object_face _ (topTable_bounded 0) _
  erw [he,generatorCylinder_endpoint,lift_top]

lemma verticalObject_source (c : X.Objects) :
    (tensorFunctor.obj X).source 0 (verticalObject c) = ((tensorEndpoint false).app X).map c.val :=
  verticalObject_face c false

lemma verticalObject_target (c : X.Objects) :
    (tensorFunctor.obj X).target 0 (verticalObject c) = ((tensorEndpoint true).app X).map c.val :=
  verticalObject_face c true

lemma verticalObject_natural (F : X ⟶ Y) (c : X.Objects) :
    (tensorFunctor.map F).map (verticalObject c) = verticalObject (F.objects c) := by
  apply tensorFunctor_map_generator

lemma chainComparison_verticalObject (c : M.nu.Objects) :
    (chainComparison M).map (verticalObject c) = verticalTable c.val := by
  change (chainComparison M).map ((tensorPresentation M.nu).generator ⟨0,c,_⟩) = _
  erw [chainComparison_generator,tableCylinder_vertical]
  exact congrArg verticalTable c.property

lemma composite_bounded (C : OmegaCategory.{u}) {n k : ℕ} (hkn : k < n)
    (x y : C.Cell) (hx : C.source n x = x) (hy : C.source n y = y)
    (h : C.target k x = C.source k y) : C.source n (C.join k x y) = C.join k x y := by
  rw [C.join_source_gt n k x y hkn h,hx,hy]

def crossingEdge (l : X.Cell) (c : X.Objects) (r : X.Cell) : (tensorFunctor.obj X).Cell :=
  (tensorFunctor.obj X).join 0
    ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalObject c))
    (((tensorEndpoint true).app X).map r)

lemma crossingEdge_left_matching (l : X.Cell) (c : X.Objects)
    (hl : X.target 0 l = c.val) :
    (tensorFunctor.obj X).target 0 (((tensorEndpoint false).app X).map l) =
      (tensorFunctor.obj X).source 0 (verticalObject c) := by
  rw [verticalObject_source,← ((tensorEndpoint false).app X).map_target]
  exact congrArg ((tensorEndpoint false).app X).map hl

lemma crossingEdge_right_matching (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).target 0
      ((tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map l) (verticalObject c)) =
        (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map r) := by
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl (crossingEdge_left_matching l c hl),
    verticalObject_target,← ((tensorEndpoint true).app X).map_source]
  exact congrArg ((tensorEndpoint true).app X).map hr.symm

lemma crossingEdge_bounded (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val)
    (hld : X.source 1 l = l) (hrd : X.source 1 r = r) :
    (tensorFunctor.obj X).source 1 (crossingEdge l c r) = crossingEdge l c r := by
  apply composite_bounded _ (by omega : 0 < 1) _ _ _ _ (crossingEdge_right_matching l c r hl hr)
  · apply composite_bounded _ (by omega : 0 < 1) _ _ _ (verticalObject_bounded c)
      (crossingEdge_left_matching l c hl)
    exact (((tensorEndpoint false).app X).map_source 1 l).symm.trans
      (congrArg ((tensorEndpoint false).app X).map hld)
  · exact (((tensorEndpoint true).app X).map_source 1 r).symm.trans
      (congrArg ((tensorEndpoint true).app X).map hrd)

lemma chainComparison_crossingEdge (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) :
    (chainComparison M).map (crossingEdge l c r) =
      M.cylinder.nu.join 0 (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l)
        (verticalTable c.val)) ((M.cylinderEndpoint true).table r) := by
  unfold crossingEdge
  erw [(chainComparison M).map_join 0 _ _ (crossingEdge_right_matching (X := M.nu) l c r hl hr),
    (chainComparison M).map_join 0 _ _ (crossingEdge_left_matching (X := M.nu) l c hl)]
  rw [chainComparison_endpoint_apply,chainComparison_endpoint_apply,chainComparison_verticalObject]

def crossingEdgeLift (t : Table M.cylinder) (hs : CylinderTables.label t false = 0)
    (ht : CylinderTables.label t true = 1) (hb : truncate 1 false t = t) :
    (tensorFunctor.obj M.nu).Cell :=
  crossingEdge (CylinderTables.leftProfile t hs ht)
    ⟨CylinderTables.crossingProfile t hs ht, CylinderTables.crossingProfile_bounded t hs ht hb⟩
    (CylinderTables.rightProfile t hs ht)

lemma crossingEdgeLift_bounded (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : CylinderTables.label t false = 0) (ht : CylinderTables.label t true = 1)
    (hb : truncate 1 false t = t) :
    (tensorFunctor.obj M.nu).source 1 (crossingEdgeLift t hs ht hb) = crossingEdgeLift t hs ht hb :=
  crossingEdge_bounded _ _ _ (CylinderTables.crossing_edge_left_target hM t hs ht hb)
    (CylinderTables.crossing_edge_right_source hM t hs ht hb)
    (CylinderTables.leftProfile_bounded t hs ht hb) (CylinderTables.rightProfile_bounded t hs ht hb)

lemma chainComparison_crossingEdgeLift (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hs : CylinderTables.label t false = 0) (ht : CylinderTables.label t true = 1)
    (hb : truncate 1 false t = t) :
    (chainComparison M).map (crossingEdgeLift t hs ht hb) = t := by
  erw [crossingEdgeLift,chainComparison_crossingEdge _ _ _
    (CylinderTables.crossing_edge_left_target hM t hs ht hb)
    (CylinderTables.crossing_edge_right_source hM t hs ht hb)]
  erw [M.cylinder.nu.join_eq 0 _ _ (CylinderTables.crossing_edge_matching_left hM t hs ht hb),
    M.cylinder.nu.join_eq 0 _ _ (CylinderTables.crossing_edge_matching_right hM t hs ht hb)]
  exact CylinderTables.crossing_edge_factor hM t hs ht hb

theorem chainComparison_edges_surjective (hM : PositiveAcyclic M) (t : Table M.cylinder)
    (hb : truncate 1 false t = t) :
    ∃ x : (tensorFunctor.obj M.nu).Cell,
      (tensorFunctor.obj M.nu).source 1 x = x ∧ (chainComparison M).map x = t := by
  rcases CylinderTables.endpoint_or_crossing hM t with ⟨a,ha⟩ | ⟨hs,ht⟩
  · refine ⟨((tensorEndpoint a).app M.nu).map (CylinderTables.project t), ?_,
      (chainComparison_endpoint_apply a _).trans ha.symm⟩
    erw [← ((tensorEndpoint a).app M.nu).map_source]
    congr 1
    change truncate 1 false (M.cylinderProjection.table t) = M.cylinderProjection.table t
    rw [← Hom.table_truncate,hb]
  · exact ⟨crossingEdgeLift t hs ht hb, crossingEdgeLift_bounded hM t hs ht hb,
      chainComparison_crossingEdgeLift hM t hs ht hb⟩
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open DirectedComplex

theorem complexPositiveAcyclic (n : ℕ) : PositiveAcyclic (complex.{u} n) where
  augmentation_nonneg _ hx := mass_nonneg hx
  augmentation_zero _ hx h := (mass_eq_zero_iff hx).mp h
  cycle_zero _ _ hx h := positive_cycle_zero _ hx h

end Thomason.GlobeComplex

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y : OmegaCategory.{u}}

lemma crossingEdge_source (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).source 0 (crossingEdge l c r) =
      ((tensorEndpoint false).app X).map (X.source 0 l) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl (crossingEdge_left_matching l c hl),
    ← ((tensorEndpoint false).app X).map_source]
  rfl

lemma crossingEdge_target (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).target 0 (crossingEdge l c r) =
      ((tensorEndpoint true).app X).map (X.target 0 r) := by
  unfold crossingEdge
  rw [(tensorFunctor.obj X).join_target_le 0 0 _ _ le_rfl (crossingEdge_right_matching l c r hl hr),
    ← ((tensorEndpoint true).app X).map_target]
  rfl

lemma tensorFunctor_map_endpoint (F : X ⟶ Y) (a : Bool) (x : X.Cell) :
    (tensorFunctor.map F).map (((tensorEndpoint a).app X).map x) =
      ((tensorEndpoint a).app Y).map (F.map x) :=
  (congrArg (fun f : X ⟶ tensorFunctor.obj Y => f.map x) ((tensorEndpoint a).naturality F)).symm

lemma tensorFunctor_map_crossingEdge (F : X ⟶ Y) (l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.map F).map (crossingEdge l c r) = crossingEdge (F.map l) (F.objects c) (F.map r) := by
  unfold crossingEdge
  rw [(tensorFunctor.map F).map_join 0 _ _ (crossingEdge_right_matching l c r hl hr),
    (tensorFunctor.map F).map_join 0 _ _ (crossingEdge_left_matching l c hl),
    tensorFunctor_map_endpoint,tensorFunctor_map_endpoint,verticalObject_natural]

inductive EdgeNormal (X : OmegaCategory.{u}) : (tensorFunctor.obj X).Cell → Prop
  | endpoint (a : Bool) (x : X.Cell) (hx : X.source 1 x = x) :
      EdgeNormal X (((tensorEndpoint a).app X).map x)
  | crossing (l : X.Cell) (c : X.Objects) (r : X.Cell)
      (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val)
      (hdl : X.source 1 l = l) (hdr : X.source 1 r = r) :
      EdgeNormal X (crossingEdge l c r)

lemma EdgeNormal.bounded {z : (tensorFunctor.obj X).Cell} (hz : EdgeNormal X z) :
    (tensorFunctor.obj X).source 1 z = z := by
  cases hz with
  | endpoint a x hx => exact (((tensorEndpoint a).app X).map_source 1 x).symm.trans (congrArg ((tensorEndpoint a).app X).map hx)
  | crossing l c r hl hr hdl hdr => exact crossingEdge_bounded l c r hl hr hdl hdr

lemma EdgeNormal.map (F : X ⟶ Y) {z : (tensorFunctor.obj X).Cell} (hz : EdgeNormal X z) :
    EdgeNormal Y ((tensorFunctor.map F).map z) := by
  cases hz with
  | endpoint a x hx =>
    rw [tensorFunctor_map_endpoint]
    exact .endpoint a (F.map x) ((F.map_source 1 x).symm.trans (congrArg F.map hx))
  | crossing l c r hl hr hdl hdr =>
    rw [tensorFunctor_map_crossingEdge F l c r hl hr]
    exact .crossing (F.map l) (F.objects c) (F.map r)
      ((F.map_target 0 l).symm.trans (congrArg F.map hl))
      ((F.map_source 0 r).symm.trans (congrArg F.map hr))
      ((F.map_source 1 l).symm.trans (congrArg F.map hdl))
      ((F.map_source 1 r).symm.trans (congrArg F.map hdr))

lemma EdgeNormal.face_zero {z : (tensorFunctor.obj X).Cell} (hz : EdgeNormal X z) (b : Bool) :
    EdgeNormal X ((tensorFunctor.obj X).face 0 b z) := by
  cases hz with
  | endpoint a x hx =>
    rw [← ((tensorEndpoint a).app X).map_face]
    exact .endpoint a _ (X.source_fixed_upwards (by omega : 0 ≤ 1) (by
      change X.face 0 false (X.face 0 b x) = X.face 0 b x
      rw [X.face_face]; simp))
  | crossing l c r hl hr hdl hdr =>
    cases b
    · change EdgeNormal X ((tensorFunctor.obj X).source 0 _)
      rw [crossingEdge_source l c r hl hr]
      exact .endpoint false _ (X.source_fixed_upwards (by omega : 0 ≤ 1) (X.source_source_self 0 l))
    · change EdgeNormal X ((tensorFunctor.obj X).target 0 _)
      rw [crossingEdge_target l c r hl hr]
      exact .endpoint true _ (X.source_fixed_upwards (by omega : 0 ≤ 1) (X.source_target_self 0 r))

lemma generatorCylinder_as_map (n : ℕ) (x : X.Cells n) (z : Table (K.{u} n)) :
    (generatorCylinder n x).map z =
      (tensorFunctor.map (GlobeComplex.lift x.val x.property)).map ((globeTensorIso n).inv.map z) := by
  change _ = (tensorFunctor.map (GlobeComplex.lift x.val x.property)).map
    ((tensorPresentation (complex n).nu).generator ⟨n,⟨topTable n,topTable_bounded n⟩,z⟩)
  erw [tensorFunctor_map_generator]
  simp only [lift_top]
  rfl

lemma globe_inv_edge_normal (n : ℕ) (t : Table (K.{u} n)) (ht : truncate 1 false t = t) :
    EdgeNormal (complex n).nu ((globeTensorIso n).inv.map t) := by
  rcases CylinderTables.endpoint_or_crossing (complexPositiveAcyclic n) t with ⟨a,ha⟩ | ⟨hs,he⟩
  · have hp : truncate 1 false (CylinderTables.project t) = CylinderTables.project t := by
      change truncate 1 false ((complex n).cylinderProjection.table t) = _
      rw [← Hom.table_truncate,ht]
      rfl
    have him : (chainComparison (complex n)).map (((tensorEndpoint a).app (complex n).nu).map
        (CylinderTables.project t)) = t := (chainComparison_endpoint_apply a _).trans ha.symm
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hback := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map (((tensorEndpoint a).app (complex n).nu).map (CylinderTables.project t))) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hback
    rw [hback] at hi
    rw [← hi]
    exact .endpoint a _ hp
  · have him := chainComparison_crossingEdgeLift (complexPositiveAcyclic n) t hs he ht
    rw [chainComparison_globe] at him
    have hi := congrArg (globeTensorIso n).inv.map him
    have hback := congrArg (fun F : tensorFunctor.obj (complex n).nu ⟶ tensorFunctor.obj (complex n).nu =>
      F.map (crossingEdgeLift t hs he ht)) (globeTensorIso n).hom_inv_id
    change (globeTensorIso n).inv.map ((globeTensorIso n).hom.map _) = _ at hback
    rw [hback] at hi
    rw [← hi]
    exact .crossing _ _ _
      (CylinderTables.crossing_edge_left_target (complexPositiveAcyclic n) t hs he ht)
      (CylinderTables.crossing_edge_right_source (complexPositiveAcyclic n) t hs he ht)
      (CylinderTables.leftProfile_bounded t hs he ht)
      (CylinderTables.rightProfile_bounded t hs he ht)

lemma generatorCylinder_edge_normal (n : ℕ) (x : X.Cells n) (t : Table (K.{u} n))
    (ht : truncate 1 false t = t) : EdgeNormal X ((generatorCylinder n x).map t) := by
  rw [generatorCylinder_as_map]
  exact (globe_inv_edge_normal n t ht).map _
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X : OmegaCategory.{u}}

lemma endpoint_source (a : Bool) (k : ℕ) (x : X.Cell) :
    (tensorFunctor.obj X).source k (((tensorEndpoint a).app X).map x) =
      ((tensorEndpoint a).app X).map (X.source k x) := (((tensorEndpoint a).app X).map_source k x).symm

lemma endpoint_target (a : Bool) (k : ℕ) (x : X.Cell) :
    (tensorFunctor.obj X).target k (((tensorEndpoint a).app X).map x) =
      ((tensorEndpoint a).app X).map (X.target k x) := (((tensorEndpoint a).app X).map_target k x).symm

lemma endpoint_join_crossing (x l : X.Cell) (c : X.Objects) (r : X.Cell)
    (hxl : X.target 0 x = X.source 0 l) (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) :
    (tensorFunctor.obj X).join 0 (((tensorEndpoint false).app X).map x) (crossingEdge l c r) =
      crossingEdge (X.join 0 x l) c r := by
  let e₀ := ((tensorEndpoint false).app X)
  let e₁ := ((tensorEndpoint true).app X)
  have h₁ : (tensorFunctor.obj X).target 0 (e₀.map x) = (tensorFunctor.obj X).source 0 (e₀.map l) :=
    e₀.map_composable hxl
  have h₂ := crossingEdge_left_matching l c hl
  have h₃ := crossingEdge_right_matching l c r hl hr
  unfold crossingEdge
  erw [e₀.map_join 0 x l hxl]
  rw [(tensorFunctor.obj X).join_assoc 0 (e₀.map x) (e₀.map l) (verticalObject c) h₁ h₂]
  rw [(tensorFunctor.obj X).join_assoc 0 (e₀.map x) _ (e₁.map r) _ h₃]
  rw [(tensorFunctor.obj X).join_source_le 0 0 _ _ le_rfl h₂]
  exact h₁

lemma crossing_join_endpoint (l : X.Cell) (c : X.Objects) (r y : X.Cell)
    (hl : X.target 0 l = c.val) (hr : X.source 0 r = c.val) (hry : X.target 0 r = X.source 0 y) :
    (tensorFunctor.obj X).join 0 (crossingEdge l c r) (((tensorEndpoint true).app X).map y) =
      crossingEdge l c (X.join 0 r y) := by
  have h₁ := crossingEdge_right_matching l c r hl hr
  have h₂ : (tensorFunctor.obj X).target 0 (((tensorEndpoint true).app X).map r) =
      (tensorFunctor.obj X).source 0 (((tensorEndpoint true).app X).map y) :=
    ((tensorEndpoint true).app X).map_composable hry
  unfold crossingEdge
  erw [((tensorEndpoint true).app X).map_join 0 r y hry,
    (tensorFunctor.obj X).join_assoc 0 _ _ _ h₁ h₂]

lemma EdgeNormal.join {x y : (tensorFunctor.obj X).Cell} (hx : EdgeNormal X x) (hy : EdgeNormal X y)
    (h : (tensorFunctor.obj X).target 0 x = (tensorFunctor.obj X).source 0 y) :
    EdgeNormal X ((tensorFunctor.obj X).join 0 x y) := by
  cases hx with
  | endpoint a x hx =>
    cases hy with
    | endpoint b y hy =>
      rw [endpoint_target,endpoint_source] at h
      obtain ⟨hab,hxy⟩ := (tensorEndpoint_eq_iff a b _ _).mp h
      subst b
      rw [← ((tensorEndpoint a).app X).map_join 0 x y hxy]
      exact .endpoint a _ (composite_bounded X (by omega : 0 < 1) x y hx hy hxy)
    | crossing l c r hl hr hdl hdr =>
      rw [endpoint_target,crossingEdge_source l c r hl hr] at h
      obtain ⟨ha,hxl⟩ := (tensorEndpoint_eq_iff a false _ _).mp h
      subst a
      rw [endpoint_join_crossing x l c r hxl hl hr]
      exact .crossing _ c r ((X.join_target_le 0 0 x l le_rfl hxl).trans hl) hr
        (composite_bounded X (by omega : 0 < 1) x l hx hdl hxl) hdr
  | crossing l c r hl hr hdl hdr =>
    cases hy with
    | endpoint a y hy =>
      rw [crossingEdge_target l c r hl hr,endpoint_source] at h
      obtain ⟨ha,hry⟩ := (tensorEndpoint_eq_iff true a _ _).mp h
      subst a
      rw [crossing_join_endpoint l c r y hl hr hry]
      exact .crossing l c _ hl ((X.join_source_le 0 0 r y le_rfl hry).trans hr) hdl
        (composite_bounded X (by omega : 0 < 1) r y hdr hy hry)
    | crossing l' c' r' hl' hr' hdl' hdr' =>
      rw [crossingEdge_target l c r hl hr,crossingEdge_source l' c' r' hl' hr'] at h
      exact False.elim (Bool.noConfusion ((tensorEndpoint_eq_iff true false _ _).mp h).1)

lemma tensor_one_faces_normal (z : (tensorFunctor.obj X).Cell) (b : Bool) :
    EdgeNormal X ((tensorFunctor.obj X).face 1 b z) := by
  suffices h : ∀ b : Bool, EdgeNormal X ((tensorFunctor.obj X).face 1 b z) from h b
  apply (tensorPresentation X).cells_induction (fun z => ∀ b : Bool,
    EdgeNormal X ((tensorFunctor.obj X).face 1 b z))
  · rintro ⟨n,x,t⟩ b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((generatorCylinder n x).map t))
    erw [← (generatorCylinder n x).map_face]
    have he : (K n).nu.face 1 b t = truncate 1 b t := by cases b <;> rfl
    rw [he]
    exact generatorCylinder_edge_normal n x _ (by
      erw [truncate_truncate]; simp)
  · intro k x hx b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((tensorFunctor.obj X).face k false x))
    erw [(tensorFunctor.obj X).face_face]
    by_cases hk : 1 < k
    · rw [ite_eq_left hk]; exact hx b
    · rw [ite_eq_right hk]
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · have he := (hx false).face_zero false
        erw [(tensorFunctor.obj X).face_face,ite_eq_left (by omega : 0 < 1)] at he
        exact he
      · exact hx false
  · intro k x hx b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((tensorFunctor.obj X).face k true x))
    erw [(tensorFunctor.obj X).face_face]
    by_cases hk : 1 < k
    · rw [ite_eq_left hk]; exact hx b
    · rw [ite_eq_right hk]
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · have he := (hx false).face_zero true
        erw [(tensorFunctor.obj X).face_face,ite_eq_left (by omega : 0 < 1)] at he
        exact he
      · exact hx true
  · intro k x y h hx hy b
    change EdgeNormal X ((tensorFunctor.obj X).face 1 b ((tensorFunctor.obj X).comp k x y h))
    cases k with
    | zero =>
      cases b
      · change EdgeNormal X ((tensorFunctor.obj X).source 1 _)
        rw [← (tensorFunctor.obj X).join_eq 0 x y h,
          (tensorFunctor.obj X).join_source_gt 1 0 x y (by omega) h]
        exact (hx false).join (hy false) ((tensorFunctor.obj X).source_composable (by omega) h)
      · change EdgeNormal X ((tensorFunctor.obj X).target 1 _)
        rw [← (tensorFunctor.obj X).join_eq 0 x y h,
          (tensorFunctor.obj X).join_target_gt 1 0 x y (by omega) h]
        exact (hx true).join (hy true) ((tensorFunctor.obj X).target_composable (by omega) h)
    | succ k =>
      cases b
      · change EdgeNormal X ((tensorFunctor.obj X).source 1 _)
        rw [(tensorFunctor.obj X).source_comp_le 1 (k+1) (by omega) x y h]
        exact hx false
      · change EdgeNormal X ((tensorFunctor.obj X).target 1 _)
        rw [(tensorFunctor.obj X).target_comp_le 1 (k+1) (by omega) x y h]
        exact hy true

lemma tensor_edge_normal (z : (tensorFunctor.obj X).Cell)
    (hz : (tensorFunctor.obj X).source 1 z = z) : EdgeNormal X z := by
  have h := tensor_one_faces_normal z false
  change EdgeNormal X ((tensorFunctor.obj X).source 1 z) at h
  rwa [hz] at h
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {M : DirectedComplex.{u}}

lemma crossing_edge_table_matching_left (l : Table M) (c : M.nu.Objects)
    (hl : truncate 0 true l = c.val) :
    truncate 0 true ((M.cylinderEndpoint false).table l) = truncate 0 false (verticalTable c.val) := by
  rw [CylinderTables.vertical_object_face c.val c.property,← Hom.table_truncate,hl]

lemma crossing_edge_table_matching_right (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) :
    M.cylinder.nu.target 0 (M.cylinder.nu.join 0 ((M.cylinderEndpoint false).table l) (verticalTable c.val)) =
      M.cylinder.nu.source 0 ((M.cylinderEndpoint true).table r) := by
  rw [M.cylinder.nu.join_target_le 0 0 _ _ le_rfl (crossing_edge_table_matching_left l c hl)]
  change truncate 0 true (verticalTable c.val) = truncate 0 false ((M.cylinderEndpoint true).table r)
  rw [CylinderTables.vertical_object_face c.val c.property,← Hom.table_truncate,hr]

lemma table_join_zero_row_succ (x y : Table M)
    (h : truncate 0 true x = truncate 0 false y) (p : ℕ) (b : Bool) :
    (M.nu.join 0 x y).row (p+1) b = x.row (p+1) b + y.row (p+1) b := by
  rw [M.nu.join_eq 0 x y h]
  change (DirectedComplex.Table.comp 0 x y h).row (p+1) b = _
  simp only [comp_row, Nat.not_lt_zero, Nat.add_one_ne_zero, ite_false]

lemma table_join_zero_row_zero (x y : Table M)
    (h : truncate 0 true x = truncate 0 false y) (b : Bool) :
    (M.nu.join 0 x y).row 0 b = if b then y.row 0 true else x.row 0 false := by
  rw [M.nu.join_eq 0 x y h]
  rfl

lemma chainComparison_crossingEdge_row_succ (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) (p : ℕ) (b : Bool) :
    ((chainComparison M).map (crossingEdge l c r)).row (p+1) b =
      (l.row (p+1) b,r.row (p+1) b,c.val.row p b) := by
  rw [chainComparison_crossingEdge l c r hl hr,
    table_join_zero_row_succ _ _ (crossing_edge_table_matching_right l c r hl hr),
    table_join_zero_row_succ _ _ (crossing_edge_table_matching_left l c hl)]
  change M.cylinderEndpointMap false (p+1) (l.row (p+1) b) + verticalRow c.val (p+1) b +
    M.cylinderEndpointMap true (p+1) (r.row (p+1) b) = _
  have hz : c.val.row (p+1) b = 0 := row_above_fixed c.val c.property (by omega) b
  have hv : verticalRow c.val (p+1) b = (0,0,c.val.row p b) := by
    simp only [verticalRow,hz]
    split_ifs <;> rfl
  rw [hv]
  change (l.row (p+1) b,0,0) + (0,0,c.val.row p b) + (0,r.row (p+1) b,0) = _
  simp only [Prod.mk_add_mk,add_zero,zero_add]

lemma chainComparison_crossingEdge_row_zero (l : Table M) (c : M.nu.Objects) (r : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val) (b : Bool) :
    ((chainComparison M).map (crossingEdge l c r)).row 0 b =
      if b then (0,r.row 0 true) else (l.row 0 false,0) := by
  rw [chainComparison_crossingEdge l c r hl hr,
    table_join_zero_row_zero _ _ (crossing_edge_table_matching_right l c r hl hr),
    table_join_zero_row_zero _ _ (crossing_edge_table_matching_left l c hl)]
  cases b <;> rfl

lemma chainComparison_crossingEdge_injective
    (l l' : Table M) (c c' : M.nu.Objects) (r r' : Table M)
    (hl : truncate 0 true l = c.val) (hr : truncate 0 false r = c.val)
    (hl' : truncate 0 true l' = c'.val) (hr' : truncate 0 false r' = c'.val)
    (he : (chainComparison M).map (crossingEdge l c r) =
      (chainComparison M).map (crossingEdge l' c' r')) :
    l = l' ∧ c = c' ∧ r = r' := by
  have hrows (p : ℕ) (b : Bool) := congrArg (fun t : Table M.cylinder => t.row (p+1) b) he
  simp only [chainComparison_crossingEdge_row_succ l c r hl hr,
    chainComparison_crossingEdge_row_succ l' c' r' hl' hr'] at hrows
  have hc : c = c' := by
    apply Subtype.ext
    apply Table.ext
    funext p b
    exact congrArg (fun z => z.2.2) (hrows p b)
  subst c'
  have he₀ (b : Bool) := congrArg (fun t : Table M.cylinder => t.row 0 b) he
  simp only [chainComparison_crossingEdge_row_zero l c r hl hr,
    chainComparison_crossingEdge_row_zero l' c r' hl' hr'] at he₀
  have he_l : l = l' := by
    ext p b
    cases p with
    | succ p => exact congrArg Prod.fst (hrows p b)
    | zero =>
      cases b
      · exact congrArg Prod.fst (he₀ false)
      · have h := congrArg (fun t : Table M => t.row 0 false) (hl.trans hl'.symm)
        exact h
  have he_r : r = r' := by
    ext p b
    cases p with
    | succ p => exact congrArg (fun z => z.2.1) (hrows p b)
    | zero =>
      cases b
      · have h := congrArg (fun t : Table M => t.row 0 false) (hr.trans hr'.symm)
        exact h
      · exact congrArg Prod.snd (he₀ true)
  exact ⟨he_l,rfl,he_r⟩

lemma chainComparison_edges_injective (x y : (tensorFunctor.obj M.nu).Cell)
    (hx : (tensorFunctor.obj M.nu).source 1 x = x) (hy : (tensorFunctor.obj M.nu).source 1 y = y)
    (he : (chainComparison M).map x = (chainComparison M).map y) : x = y := by
  have hnx := tensor_edge_normal x hx
  have hny := tensor_edge_normal y hy
  cases hnx with
  | endpoint a x hx =>
    exact ((chainComparison_endpoint_fiber y a x).mp
      (he.symm.trans (chainComparison_endpoint_apply a x))).symm
  | crossing l c r hl hr hdl hdr =>
    cases hny with
    | endpoint a y hy =>
      exact (chainComparison_endpoint_fiber _ a y).mp (he.trans (chainComparison_endpoint_apply a y))
    | crossing l' c' r' hl' hr' hdl' hdr' =>
      obtain ⟨rfl,rfl,rfl⟩ := chainComparison_crossingEdge_injective l l' c c' r r' hl hr hl' hr' he
      rfl

theorem chainComparison_edges_bijective (hM : PositiveAcyclic M) :
    Function.Bijective ((chainComparison M).onCells 1) := by
  constructor
  · intro x y he
    apply Subtype.ext
    exact chainComparison_edges_injective x.val y.val x.property y.property (congrArg Subtype.val he)
  · intro t
    obtain ⟨x,hx,he⟩ := chainComparison_edges_surjective hM t.val t.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩

theorem chainComparison_poset_edges_bijective (P : Type u) [PartialOrder P] :
    Function.Bijective
      ((chainComparison (NormalizedChains.complex P)).onCells 1) :=
  chainComparison_edges_bijective (NormalizedChains.complexPositiveAcyclic P)
end Thomason.GrayRecursive.IntervalHom

end

end OAI
