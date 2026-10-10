import Mathlib
import OAI.CategoryTheory.Thomason.RectangleComposition

namespace OAI

/-! Cylinder Faces. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma suspend_composable {n k : ℕ} {x y : Table (complex.{u} n)}
    (h : truncate k true x = truncate k false y) :
    truncate (k+1) true (suspendTable x) = truncate (k+1) false (suspendTable y) := by
  rw [← suspendTable_truncate, ← suspendTable_truncate, h]

lemma suspend_comp {n k : ℕ} (x y : Table (complex.{u} n))
    (h : truncate k true x = truncate k false y)
    (h' : truncate (k+1) true (suspendTable x) = truncate (k+1) false (suspendTable y)) :
    suspendTable (DirectedComplex.Table.comp k x y h) =
      DirectedComplex.Table.comp (k+1) (suspendTable x) (suspendTable y) h' := by
  ext p b
  cases p with
  | zero => simp
  | succ p =>
    simp only [suspendTable_succ, comp_row, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    erw [apply_ite (shiftDown n p).symm, apply_ite (shiftDown n p).symm,
      apply_ite (shiftDown n p).symm, map_add]
    rfl

def globeHom (n : ℕ) : OmegaCategory.Functor (complex.{u} n).nu
    ((complex.{u} (n+1)).nu.homCategory (vertex n false) (vertex n true)) where
  map x := ⟨suspendTable x, suspend_truncate_zero false x, suspend_truncate_zero true x⟩
  map_source k x := Subtype.ext (suspendTable_truncate x k false)
  map_target k x := Subtype.ext (suspendTable_truncate x k true)
  map_comp k x y h h' := Subtype.ext (suspend_comp (k := k) x y h (congrArg Subtype.val h'))

def globeHomMap {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) :
    OmegaCategory.Functor (complex.{u} n).nu
      (Y.homCategory (F.map (vertex n false)) (F.map (vertex n true))) :=
  OmegaCategory.Functor.comp (globeHom n) (F.homMap (vertex n false) (vertex n true))

lemma globe_horizontal_match {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    Y.target 0 (F.map (topTable (n+1))) = Y.source 0 (G.map (topTable (n+1))) := by
  erw [← F.map_target, ← G.map_source]
  exact h

lemma globe_horizontal_fixed {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    Y.source (n+1) (Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1)))) =
      Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) := by
  erw [Y.join_source_gt (n+1) 0 _ _ (by omega) (globe_horizontal_match F G h), ← F.map_source, ← G.map_source]
  change Y.join 0 (F.map (truncate (n+1) false (topTable (n+1))))
    (G.map (truncate (n+1) false (topTable (n+1)))) = _
  rw [topTable_bounded]

def globeHorizontal {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    OmegaCategory.Functor (complex.{u} (n+1)).nu Y :=
  GlobeComplex.lift _ (globe_horizontal_fixed F G h)

@[simp] lemma globeHorizontal_vertex {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) (a : Bool) :
    (globeHorizontal F G h).map (vertex n a) = if a then G.map (vertex n true) else F.map (vertex n false) := by
  erw [vertex, ← face_nu, (globeHorizontal F G h).map_face]
  have ht : (globeHorizontal F G h).map (topTable (n+1)) =
      Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) := lift_top _ _
  rw [ht]
  cases a
  · change Y.source 0 _ = _
    erw [Y.join_source_le 0 0 _ _ le_rfl (globe_horizontal_match F G h), ← F.map_source]; rfl
  · change Y.target 0 _ = _
    erw [Y.join_target_le 0 0 _ _ le_rfl (globe_horizontal_match F G h), ← G.map_target]; rfl

@[simp] lemma globeHorizontal_suspend {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) (x : Table (complex.{u} n)) :
    (globeHorizontal F G h).map (suspendTable x) =
      Y.join 0 (F.map (suspendTable x)) (G.map (suspendTable x)) := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  erw [he, suspendTable_eq_face, ← face_nu, (globeHorizontal F G h).map_face, F.map_face, G.map_face]
  have ht : (globeHorizontal F G h).map (topTable (n+1)) =
      Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) := lift_top _ _
  rw [ht]
  cases a
  · exact Y.join_source_gt (p+1) 0 _ _ (by omega) (globe_horizontal_match F G h)
  · exact Y.join_target_gt (p+1) 0 _ _ (by omega) (globe_horizontal_match F G h)

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}}
    (D E : RectangleDiagram.{u,v} n Y) (h : D.edge true = E.edge false)

include h in
lemma horizontal_seam (a : Bool) :
    (D.ends a).map (vertex n true) = (E.ends a).map (vertex n false) := by
  cases a
  · rw [← D.edge_source, h, E.edge_source]
  · rw [← D.edge_target, h, E.edge_target]

def horizontalDiagonalOne : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose D.diagonal (homCast
    (OmegaCategory.Functor.comp (complex n).cylinderProjection.nu (globeHomMap (E.ends true)))
    (D.horizontal_seam E h true).symm rfl)

def horizontalDiagonalTwo : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose (homCast
    (OmegaCategory.Functor.comp (complex n).cylinderProjection.nu (globeHomMap (D.ends false)))
    rfl (D.horizontal_seam E h false)) E.diagonal

lemma horizontalDiagonalOne_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalOne E h).map x).val =
      Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x))) := rfl
lemma horizontalDiagonalTwo_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalTwo E h).map x).val =
      Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val := rfl

lemma horizontalDiagonal_matching : IntervalMatching (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h) := by
  intro x
  apply Subtype.ext
  rw [D.horizontalDiagonalOne_map E h, D.horizontalDiagonalTwo_map E h, project_end, project_end, D.right, E.left, h]
  exact Y.join_assoc 0 _ _ _ (by rw [← h]; exact D.end_edge_matching x) (E.edge_end_matching x)

include h in
lemma horizontal_source_match (x : Table (complex.{u} n)) (a : Bool) :
    Y.target 0 ((D.ends a).map (suspendTable x)) = Y.source 0 ((E.ends a).map (suspendTable x)) := by
  erw [← (D.ends a).map_target, ← (E.ends a).map_source]
  change (D.ends a).map (truncate 0 true (suspendTable x)) =
    (E.ends a).map (truncate 0 false (suspendTable x))
  rw [suspend_truncate_zero, suspend_truncate_zero]
  exact D.horizontal_seam E h a

def horizontal : RectangleDiagram.{u,v} n Y where
  ends a := globeHorizontal (D.ends a) (E.ends a) (D.horizontal_seam E h a)
  edge a := if a then E.edge true else D.edge false
  edge_fixed a := by cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true]; exact D.edge_fixed false; exact E.edge_fixed true
  edge_source a := by
    rw [globeHorizontal_vertex]
    cases a
    · exact D.edge_source false
    · exact E.edge_source true
  edge_target a := by
    rw [globeHorizontal_vertex]
    cases a
    · exact D.edge_target false
    · exact E.edge_target true
  diagonal := homCast (concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
    (D.horizontalDiagonal_matching E h))
    (by simp)
    (by simp)
  left x := by
    change ((concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
      (D.horizontalDiagonal_matching E h)).map (atEnd false x)).val = _
    rw [concatInterval_endpoint]
    simp only [Bool.false_eq_true, ite_false]
    rw [D.horizontalDiagonalOne_map E h, project_end, D.left, globeHorizontal_suspend]
    exact Y.join_assoc 0 _ _ _ (D.edge_end_matching x) (D.horizontal_source_match E h x true)
  right x := by
    change ((concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
      (D.horizontalDiagonal_matching E h)).map (atEnd true x)).val = _
    rw [concatInterval_endpoint]
    simp only [ite_true]
    rw [D.horizontalDiagonalTwo_map E h, project_end, E.right, globeHorizontal_suspend]
    exact (Y.join_assoc 0 _ _ _ (D.horizontal_source_match E h x false) (E.end_edge_matching x)).symm

end RectangleDiagram

def horizontalCylinder {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false))) :
    OmegaCategory.Functor (K.{u} (n+1)).nu Y :=
  ((rectangleDiagramOfFunctor F).horizontal (rectangleDiagramOfFunctor G) h).lift

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma globeHorizontal_natural {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (globeHorizontal F G h) P =
    globeHorizontal (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
      (congrArg P.map h) := by
  apply GlobeComplex.functor_ext
  change P.map ((globeHorizontal F G h).map (topTable (n+1))) = _
  rw [show (globeHorizontal F G h).map (topTable (n+1)) =
    Y.join 0 (F.map (topTable (n+1))) (G.map (topTable (n+1))) from lift_top _ _,
    show (globeHorizontal (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
      (congrArg P.map h)).map (topTable (n+1)) = _ from lift_top _ _]
  exact P.map_join 0 _ _ (globe_horizontal_match F G h)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (D E : RectangleDiagram.{u,v} n Y) (h : D.edge true = E.edge false)
    (P : OmegaCategory.Functor Y Z)

lemma map_horizontalDiagonalOne :
    OmegaCategory.Functor.comp (D.horizontalDiagonalOne E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).horizontalDiagonalOne (E.map P) (congrArg P.map h) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x)))) =
    Z.join 0 (P.map (D.diagonal.map x).val) (P.map ((E.ends true).map (suspendTable (project x))))
  apply P.map_join
  erw [(D.diagonal.map x).property.2, D.horizontal_seam E h true, ← (E.ends true).map_source]
  exact congrArg (E.ends true).map (suspend_truncate_zero false (project x)).symm

lemma map_horizontalDiagonalTwo :
    OmegaCategory.Functor.comp (D.horizontalDiagonalTwo E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).horizontalDiagonalTwo (E.map P) (congrArg P.map h) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val) =
    Z.join 0 (P.map ((D.ends false).map (suspendTable (project x)))) (P.map (E.diagonal.map x).val)
  apply P.map_join
  erw [(E.diagonal.map x).property.1, ← D.horizontal_seam E h false, ← (D.ends false).map_target]
  exact congrArg (D.ends false).map (suspend_truncate_zero true (project x))

lemma horizontal_lift_map :
    OmegaCategory.Functor.comp (D.horizontal E h).lift P =
      ((D.map P).horizontal (E.map P) (congrArg P.map h)).lift := by
  apply functor_ext_rectangle
  · intro a x
    change P.map ((D.horizontal E h).lift.map (atEnd a x)) = _
    rw [lift_endpoint, lift_endpoint]
    exact congrArg (fun U => U.map x)
      (globeHorizontal_natural (D.ends a) (E.ends a) (D.horizontal_seam E h a) P)
  · intro a
    change P.map ((D.horizontal E h).lift.map (verticalTable (vertex n a))) = _
    rw [lift_edge, lift_edge]
    cases a <;> rfl
  · intro x
    change P.map ((D.horizontal E h).lift.map (up x)) = _
    rw [lift_up, lift_up]
    have hh := concatInterval_natural n (D.horizontalDiagonalOne E h)
      (D.horizontalDiagonalTwo E h) (D.horizontalDiagonal_matching E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
    simp only [D.map_horizontalDiagonalOne E h P, D.map_horizontalDiagonalTwo E h P] at hh
    exact congrArg (fun U => (U.map x).val) hh

end RectangleDiagram

lemma horizontalCylinder_natural {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (horizontalCylinder F G h) P =
      horizontalCylinder (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
        (congrArg P.map h) :=
  (rectangleDiagramOfFunctor F).horizontal_lift_map (rectangleDiagramOfFunctor G) h P

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

@[simp] lemma project_up {n : ℕ} (x : Table (K.{u} n)) :
    project (up x) = suspendTable (project x) := by
  ext p b
  cases p with
  | zero =>
    cases b <;> simp [up, upRow, diagonalRow, suspendTable_zero,
      project, Hom.table, cylinderProjection, cylinderProjectionMap]
  | succ p =>
    cases p with
    | zero =>
      simp only [project_row, sideRow, up, upRow, suspendTable_succ]
      erw [map_add]
      exact add_comm _ _
    | succ p =>
      simp only [project_row, sideRow, up, upRow, suspendTable_succ]
      erw [map_add]
      exact add_comm _ _

@[simp] lemma project_zero_vertical :
    project (verticalTable (topTable.{u} 0)) = topTable 0 :=
  globe_zero_unique _

def constantInterval {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) :
    OmegaCategory.Functor (K.{u} n).nu Y :=
  OmegaCategory.Functor.comp (complex n).cylinderProjection.nu F

@[simp] lemma constantInterval_map {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) (x : Table (K.{u} n)) :
    (constantInterval F).map x = F.map (project x) := rfl

@[simp] lemma constantInterval_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) (a : Bool) (x : Table (complex.{u} n)) :
    (constantInterval F).map (atEnd a x) = F.map x := by
  rw [constantInterval_map, project_end]

@[simp] lemma constantInterval_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) (a : Bool) :
    (constantInterval F).map (verticalTable (vertex n a)) = F.map (vertex n a) := by
  rw [constantInterval_map, project_vertical_vertex]

@[simp] lemma constantInterval_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) (x : Table (K.{u} n)) :
    (constantInterval F).map (up x) = F.map (suspendTable (project x)) := by
  rw [constantInterval_map, project_up]

lemma constantInterval_matching {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) :
    IntervalMatching (constantInterval F) (constantInterval F) := by
  intro x
  rw [constantInterval_endpoint, constantInterval_endpoint]

lemma constantInterval_ends {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) (a : Bool) :
    (rectangleDiagramOfFunctor (constantInterval F)).ends a = F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact constantInterval_endpoint F a x

lemma constantInterval_diagonal {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) :
    homCast (rectangleDiagramOfFunctor (constantInterval F)).diagonal
      (constantInterval_endpoint F false (vertex n false))
      (constantInterval_endpoint F true (vertex n true)) =
    constantInterval (globeHomMap F) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  exact constantInterval_up F x

lemma constantInterval_concatDiagonalOne {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) :
    (rectangleDiagramOfFunctor (constantInterval F)).concatDiagonalOne
      (rectangleDiagramOfFunctor (constantInterval F)) (constantInterval_matching F) =
    homCast (constantInterval (globeHomMap F))
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint F true (vertex n true)).symm := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (verticalTable (vertex n false)))
    ((constantInterval F).map (up x)) = F.map (suspendTable (project x))
  erw [constantInterval_edge, constantInterval_up]
  apply Y.join_left_unit
  · erw [← F.map_source]
    exact congrArg F.map (vertex_truncate n 0 false false)
  · erw [← F.map_target, ← F.map_source]
    exact congrArg F.map ((vertex_truncate n 0 false true).trans
      (suspend_truncate_zero false (project x)).symm)

lemma constantInterval_concatDiagonalTwo {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} (n+1)).nu Y) :
    (rectangleDiagramOfFunctor (constantInterval F)).concatDiagonalTwo
      (rectangleDiagramOfFunctor (constantInterval F)) (constantInterval_matching F) =
    homCast (constantInterval (globeHomMap F))
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint F true (vertex n true)).symm := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (up x))
    ((constantInterval F).map (verticalTable (vertex n true))) = F.map (suspendTable (project x))
  erw [constantInterval_edge, constantInterval_up]
  apply Y.join_right_unit
  · erw [← F.map_source]
    exact congrArg F.map (vertex_truncate n 0 true false)
  · erw [← F.map_target, ← F.map_source]
    exact congrArg F.map ((suspend_truncate_zero true (project x)).trans
      (vertex_truncate n 0 true false).symm)

lemma homCast_constantInterval {n : ℕ} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (hac : a = c) (hbd : b = d) :
    homCast (constantInterval F) hac hbd = constantInterval (homCast F hac hbd) := rfl

lemma concatInterval_constant (n : ℕ) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (complex.{u} n).nu Y) :
    concatInterval (constantInterval F) (constantInterval F) (constantInterval_matching F) =
      constantInterval F := by
  induction n generalizing Y with
  | zero =>
    apply OmegaCategory.Functor.ext
    funext x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he, concatInterval_endpoint]
      cases a <;> simp
    · rw [he, concatInterval_zero_vertical, constantInterval_map, project_zero_vertical]
      apply Y.join_left_unit
      · erw [← F.map_source]
        exact congrArg F.map (topTable_bounded 0)
      · erw [← F.map_target, ← F.map_source]
        exact congrArg F.map (show truncate 0 true (topTable 0) = truncate 0 false (topTable 0) by
          rw [globe_zero_unique (truncate 0 true _), globe_zero_unique (truncate 0 false _)])
  | succ n ih =>
    apply functor_ext_rectangle
    · intro a x
      rw [concatInterval_endpoint]
      cases a <;> simp
    · intro a
      rw [concatInterval_succ_edge, constantInterval_edge]
      apply Y.join_left_unit
      · erw [← F.map_source]; exact congrArg F.map (vertex_truncate n 0 a false)
      · erw [← F.map_target, ← F.map_source]
        exact congrArg F.map ((vertex_truncate n 0 a true).trans (vertex_truncate n 0 a false).symm)
    · intro x
      rw [concatInterval_succ_up]
      simp only [constantInterval_concatDiagonalOne, constantInterval_concatDiagonalTwo,
        homCast_constantInterval]
      erw [ih]
      exact (constantInterval_up F x).symm

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def globeHorizontalHom {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    OmegaCategory.Functor (complex.{u} n).nu
      (Y.homCategory (F.map (vertex n false)) (G.map (vertex n true))) :=
  homCompose (globeHomMap F) (homCast (globeHomMap G) h.symm rfl)

lemma constantInterval_horizontal_match {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    (constantInterval F).map (verticalTable (vertex n true)) =
      (constantInterval G).map (verticalTable (vertex n false)) := by
  rw [constantInterval_edge, constantInterval_edge, h]

lemma constantInterval_horizontalDiagonalOne {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    (rectangleDiagramOfFunctor (constantInterval F)).horizontalDiagonalOne
      (rectangleDiagramOfFunctor (constantInterval G)) (constantInterval_horizontal_match F G h) =
    constantInterval (homCast (globeHorizontalHom F G h)
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint G true (vertex n true)).symm) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (up x))
    ((constantInterval G).map (atEnd true (suspendTable (project x)))) =
      Y.join 0 (F.map (suspendTable (project x))) (G.map (suspendTable (project x)))
  erw [constantInterval_up, constantInterval_endpoint]

lemma constantInterval_horizontalDiagonalTwo {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    (rectangleDiagramOfFunctor (constantInterval F)).horizontalDiagonalTwo
      (rectangleDiagramOfFunctor (constantInterval G)) (constantInterval_horizontal_match F G h) =
    constantInterval (homCast (globeHorizontalHom F G h)
      (constantInterval_endpoint F false (vertex n false)).symm
      (constantInterval_endpoint G true (vertex n true)).symm) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 ((constantInterval F).map (atEnd false (suspendTable (project x))))
    ((constantInterval G).map (up x)) =
      Y.join 0 (F.map (suspendTable (project x))) (G.map (suspendTable (project x)))
  erw [constantInterval_up, constantInterval_endpoint]

lemma horizontalCylinder_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (a : Bool) (x : Table (complex.{u} (n+1))) :
    (horizontalCylinder F G h).map (atEnd a x) =
      (globeHorizontal ((rectangleDiagramOfFunctor F).ends a) ((rectangleDiagramOfFunctor G).ends a)
        ((rectangleDiagramOfFunctor F).horizontal_seam (rectangleDiagramOfFunctor G) h a)).map x :=
  RectangleDiagram.lift_endpoint _ a x

lemma horizontalCylinder_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (a : Bool) :
    (horizontalCylinder F G h).map (verticalTable (vertex n a)) =
      if a then G.map (verticalTable (vertex n true)) else F.map (verticalTable (vertex n false)) :=
  RectangleDiagram.lift_edge _ a

lemma horizontalCylinder_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (x : Table (K.{u} n)) :
    (horizontalCylinder F G h).map (up x) =
      ((concatInterval ((rectangleDiagramOfFunctor F).horizontalDiagonalOne (rectangleDiagramOfFunctor G) h)
      ((rectangleDiagramOfFunctor F).horizontalDiagonalTwo (rectangleDiagramOfFunctor G) h)
      ((rectangleDiagramOfFunctor F).horizontalDiagonal_matching (rectangleDiagramOfFunctor G) h)).map x).val :=
  RectangleDiagram.lift_up _ x

lemma horizontalCylinder_constant {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : F.map (vertex n true) = G.map (vertex n false)) :
    horizontalCylinder (constantInterval F) (constantInterval G) (constantInterval_horizontal_match F G h) =
      constantInterval (globeHorizontal F G h) := by
  apply functor_ext_rectangle
  · intro a x
    rw [horizontalCylinder_endpoint, constantInterval_endpoint]
    simp only [constantInterval_ends]
  · intro a
    simp only [horizontalCylinder_edge, constantInterval_edge, globeHorizontal_vertex]
  · intro x
    rw [horizontalCylinder_up]
    simp only [constantInterval_horizontalDiagonalOne F G h, constantInterval_horizontalDiagonalTwo F G h]
    erw [concatInterval_constant, constantInterval_up, globeHorizontal_suspend]
    rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma faceMap_vertex (n k : ℕ) (b a : Bool) :
    (faceMap.{u} (n+1) (k+1) b).nu.map (vertex k a) = vertex n a := by
  erw [vertex, ← face_nu, OmegaCategory.Functor.map_face, faceMap_top]
  rw [face_nu]
  change truncate 0 a (truncate (k+1) b (topTable (n+1))) = vertex n a
  rw [truncate_truncate, ite_eq_left (show 0 < k+1 by omega)]
  rfl

lemma faceMap_suspend (n k : ℕ) (b : Bool) (x : Table (complex.{u} k)) :
    (faceMap.{u} (n+1) (k+1) b).nu.map (suspendTable x) =
      suspendTable ((faceMap.{u} n k b).nu.map x) := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  rw [he, suspendTable_eq_face]
  erw [← face_nu (k+1) (p+1) a (topTable (k+1)), OmegaCategory.Functor.map_face, faceMap_top, face_nu]
  erw [← face_nu k p a (topTable k), OmegaCategory.Functor.map_face, faceMap_top, face_nu]
  change truncate (p+1) a (truncate (k+1) b (topTable (n+1))) =
    suspendTable (truncate p a (truncate k b (topTable n)))
  rw [suspendTable_truncate, suspendTable_eq_face]

lemma cylinderHom_atEnd {n m : ℕ} (f : DirectedComplex.Hom (complex.{u} n) (complex.{u} m))
    (a : Bool) (x : Table (complex.{u} n)) :
    f.cylinder.nu.map (atEnd a x) = atEnd a (f.nu.map x) := by
  have h := congrArg (fun g => g.nu.map x) (f.cylinder_endpoint a)
  exact h

lemma tensorFace_edge (n k : ℕ) (b a : Bool) :
    (faceMap.{u} (n+1) (k+1) b).cylinder.nu.map (verticalTable (vertex k a)) =
      verticalTable (vertex n a) := by
  rw [verticalTable_natural, faceMap_vertex]

lemma tensorFace_up (n k : ℕ) (b : Bool) (x : Table (K.{u} k)) :
    (faceMap.{u} (n+1) (k+1) b).cylinder.nu.map (up x) =
      up ((faceMap.{u} n k b).cylinder.nu.map x) := by
  apply generated k (fun x => (faceMap.{u} (n+1) (k+1) b).cylinder.nu.map (up x) =
    up ((faceMap.{u} n k b).cylinder.nu.map x))
  · intro a y
    cases a
    · rw [up_endpoint_false]
      change (faceMap (n+1) (k+1) b).cylinder.table _ = _
      rw [(faceMap.{u} (n+1) (k+1) b).cylinder.table_comp _ _ _ _
        ((faceMap.{u} (n+1) (k+1) b).cylinder.nu.map_composable (up_endpoint_left_matching y))]
      change DirectedComplex.Table.comp 0
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _)
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _) _ = _
      simp only [tensorFace_edge, cylinderHom_atEnd, faceMap_suspend]
      erw [up_endpoint_false]
    · rw [up_endpoint_true]
      change (faceMap (n+1) (k+1) b).cylinder.table _ = _
      rw [(faceMap.{u} (n+1) (k+1) b).cylinder.table_comp _ _ _ _
        ((faceMap.{u} (n+1) (k+1) b).cylinder.nu.map_composable (up_endpoint_right_matching y))]
      change DirectedComplex.Table.comp 0
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _)
        ((faceMap (n+1) (k+1) b).cylinder.nu.map _) _ = _
      simp only [tensorFace_edge, cylinderHom_atEnd, faceMap_suspend]
      erw [up_endpoint_true]
  · intro y
    erw [up_vertical, verticalTable_natural, faceMap_suspend, verticalTable_natural, up_vertical]
  · intro l s t h hs ht
    rw [up_comp s t h (up_composable h)]
    change (faceMap (n+1) (k+1) b).cylinder.table _ = up ((faceMap n k b).cylinder.table _)
    rw [(faceMap.{u} (n+1) (k+1) b).cylinder.table_comp _ _ _ _
      ((faceMap.{u} (n+1) (k+1) b).cylinder.nu.map_composable (up_composable h))]
    have h' := (faceMap.{u} n k b).cylinder.nu.map_composable h
    rw [(faceMap.{u} n k b).cylinder.table_comp _ _ _ h h']
    change DirectedComplex.Table.comp (l+1) _ _ _ = up (DirectedComplex.Table.comp l _ _ h')
    rw [up_comp _ _ h' (up_composable h')]
    change DirectedComplex.Table.comp (l+1)
      ((faceMap (n+1) (k+1) b).cylinder.nu.map (up s))
      ((faceMap (n+1) (k+1) b).cylinder.nu.map (up t)) _ = _
    simp only [hs, ht]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def rectangleDiagramOfTop {n : ℕ} {Y : OmegaCategory.{v}}
    (ends : Bool → OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (edge : Bool → Y.Cell)
    (ef : ∀ a, Y.source 1 (edge a) = edge a)
    (es : ∀ a, Y.source 0 (edge a) = (ends false).map (vertex n a))
    (et : ∀ a, Y.target 0 (edge a) = (ends true).map (vertex n a))
    (diag : OmegaCategory.Functor (K.{u} n).nu
      (Y.homCategory ((ends false).map (vertex n false)) ((ends true).map (vertex n true))))
    (hl : (diag.map (atEnd false (topTable n))).val =
      Y.join 0 (edge false) ((ends true).map (topTable (n+1))))
    (hr : (diag.map (atEnd true (topTable n))).val =
      Y.join 0 ((ends false).map (topTable (n+1))) (edge true)) :
    RectangleDiagram.{u,v} n Y where
  ends := ends
  edge := edge
  edge_fixed := ef
  edge_source := es
  edge_target := et
  diagonal := diag
  left x := by
    let A := OmegaCategory.Functor.comp ((complex n).cylinderEndpoint false).nu diag
    let B := homCompose (constantHom (complex.{u} n).nu (edge false)
      (ef false) (es false) (et false)) (globeHomMap (ends true))
    have h : A = B := by
      apply GlobeComplex.functor_ext
      apply Subtype.ext
      change (diag.map (atEnd false (topTable n))).val =
        Y.join 0 (edge false) ((ends true).map (suspendTable (topTable n)))
      rw [suspendTable_top]
      exact hl
    exact congrArg (fun F => (F.map x).val) h
  right x := by
    let A := OmegaCategory.Functor.comp ((complex n).cylinderEndpoint true).nu diag
    let B := homCompose (globeHomMap (ends false))
      (constantHom (complex.{u} n).nu (edge true) (ef true) (es true) (et true))
    have h : A = B := by
      apply GlobeComplex.functor_ext
      apply Subtype.ext
      change (diag.map (atEnd true (topTable n))).val =
        Y.join 0 ((ends false).map (suspendTable (topTable n))) (edge true)
      rw [suspendTable_top]
      exact hr
    exact congrArg (fun F => (F.map x).val) h

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def FaceMatching {n : ℕ} (k : ℕ) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) : Prop :=
  ∀ x : Table (K.{u} k),
    F.map ((faceMap n k true).cylinder.nu.map x) =
      G.map ((faceMap n k false).cylinder.nu.map x)

def globeComposite {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    OmegaCategory.Functor (complex.{u} n).nu Y :=
  GlobeComplex.lift (Y.join k (F.map (topTable n)) (G.map (topTable n))) (by
    erw [Y.join_source_gt n k _ _ hk h, ← F.map_source, ← G.map_source]
    change Y.join k (F.map (truncate n false (topTable n)))
      (G.map (truncate n false (topTable n))) = _
    rw [topTable_bounded])

@[simp] lemma globeComposite_top {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    (globeComposite hk F G h).map (topTable n) =
      Y.join k (F.map (topTable n)) (G.map (topTable n)) := lift_top _ _

lemma globeMatching_vertex {n k : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : Y.target (k+1) (F.map (topTable (n+1))) =
      Y.source (k+1) (G.map (topTable (n+1)))) (a : Bool) :
    F.map (vertex n a) = G.map (vertex n a) := by
  have h' := congrArg (Y.face 0 a) h
  cases a
  · change Y.source 0 _ = Y.source 0 _ at h'
    simp only [Y.source_target, ite_eq_left (show 0 < k+1 by omega), Y.source_source,
      min_eq_left (show 0 ≤ k+1 by omega)] at h'
    erw [← F.map_source, ← G.map_source] at h'
    exact h'
  · change Y.target 0 _ = Y.target 0 _ at h'
    simp only [Y.target_source, ite_eq_left (show 0 < k+1 by omega), Y.target_target,
      min_eq_left (show 0 ≤ k+1 by omega)] at h'
    erw [← F.map_target, ← G.map_target] at h'
    exact h'

lemma globeComposite_vertex {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : Y.target (k+1) (F.map (topTable (n+1))) =
      Y.source (k+1) (G.map (topTable (n+1)))) (a : Bool) :
    (globeComposite (Nat.add_lt_add_right hk 1) F G h).map (vertex n a) = F.map (vertex n a) := by
  erw [vertex, ← face_nu, OmegaCategory.Functor.map_face, globeComposite_top]
  cases a
  · change Y.source 0 _ = _
    erw [Y.join_source_le 0 (k+1) _ _ (Nat.zero_le _) h, ← F.map_source]
    rfl
  · change Y.target 0 _ = _
    erw [Y.join_target_le 0 (k+1) _ _ (Nat.zero_le _) h, ← G.map_target]
    exact (globeMatching_vertex F G h true).symm

lemma globeComposite_natural {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n)))
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (globeComposite hk F G h) P =
      globeComposite hk (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
        (P.map_composable h) := by
  apply GlobeComplex.functor_ext
  change P.map ((globeComposite hk F G h).map (topTable n)) = _
  erw [globeComposite_top, globeComposite_top, P.map_join _ _ _ h]
  rfl

lemma FaceMatching.ends {n k : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : FaceMatching k F G) (a : Bool) :
    Y.target k (F.map (atEnd a (topTable n))) =
      Y.source k (G.map (atEnd a (topTable n))) := by
  have h' := h (atEnd a (topTable k))
  rw [cylinderHom_atEnd, cylinderHom_atEnd, faceMap_top, faceMap_top] at h'
  erw [← F.map_target, ← G.map_source]
  change F.map (truncate k true (atEnd a (topTable n))) =
    G.map (truncate k false (atEnd a (topTable n)))
  simpa only [atEnd_truncate] using h'

lemma FaceMatching.edges {n k : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y} (h : FaceMatching (k+1) F G) (a : Bool) :
    F.map (verticalTable (vertex n a)) = G.map (verticalTable (vertex n a)) := by
  have h' := h (verticalTable (vertex k a))
  simpa only [tensorFace_edge] using h'

lemma FaceMatching.vertices {n k : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y} (h : FaceMatching (k+1) F G) (a b : Bool) :
    F.map (atEnd a (vertex n b)) = G.map (atEnd a (vertex n b)) := by
  have h' := h (atEnd a (vertex k b))
  simpa only [cylinderHom_atEnd, faceMap_vertex] using h'

lemma FaceMatching.natural {n k : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : FaceMatching k F G)
    (P : OmegaCategory.Functor Y Z) :
    FaceMatching k (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P) :=
  fun x => congrArg P.map (h x)

end Thomason.GrayRecursive

end

end OAI
