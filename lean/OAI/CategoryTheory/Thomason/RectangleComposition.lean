import Mathlib
import OAI.CategoryTheory.Thomason.ProperTransfer

namespace OAI

/-! Rectangle Composition. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

structure RectangleDiagram (n : ℕ) (Y : OmegaCategory.{v}) where
  ends : Bool → OmegaCategory.Functor (complex.{u} (n+1)).nu Y
  edge : Bool → Y.Cell
  edge_fixed : ∀ a, Y.source 1 (edge a) = edge a
  edge_source : ∀ a, Y.source 0 (edge a) = (ends false).map (vertex n a)
  edge_target : ∀ a, Y.target 0 (edge a) = (ends true).map (vertex n a)
  diagonal : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((ends false).map (vertex n false)) ((ends true).map (vertex n true)))
  left : ∀ x, (diagonal.map (atEnd false x)).val =
    Y.join 0 (edge false) ((ends true).map (suspendTable x))
  right : ∀ x, (diagonal.map (atEnd true x)).val =
    Y.join 0 ((ends false).map (suspendTable x)) (edge true)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} (D : RectangleDiagram.{u,v} n Y)

def interpret : RectangleCell.{u} n → Y.Cell
  | .endpoint a x => (D.ends a).map x
  | .edge a => D.edge a
  | .diagonal x => (D.diagonal.map x).val

def cellMap (x : Table (K.{u} (n+1))) : Y.Cell :=
  D.interpret ((rectangleEquiv n).symm x)

@[simp] lemma cellMap_eval (x : RectangleCell.{u} n) : D.cellMap x.eval = D.interpret x := by
  change D.interpret ((rectangleEquiv n).symm (rectangleEquiv n x)) = _
  rw [Equiv.symm_apply_apply]

@[simp] lemma cellMap_endpoint (a : Bool) (x : Table (complex.{u} (n+1))) :
    D.cellMap (atEnd a x) = (D.ends a).map x := D.cellMap_eval (.endpoint a x)
@[simp] lemma cellMap_edge (a : Bool) :
    D.cellMap (verticalTable (vertex n a)) = D.edge a := D.cellMap_eval (.edge a)
@[simp] lemma cellMap_up (x : Table (K.{u} n)) :
    D.cellMap (up x) = (D.diagonal.map x).val := D.cellMap_eval (.diagonal x)

lemma cellMap_truncate (k : ℕ) (b : Bool) (x : Table (K.{u} (n+1))) :
    D.cellMap (truncate k b x) = Y.face k b (D.cellMap x) := by
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  cases r with
  | endpoint a x =>
    simp only [RectangleCell.eval, atEnd_truncate, cellMap_endpoint]
    cases b
    · exact (D.ends a).map_source k x
    · exact (D.ends a).map_target k x
  | edge a =>
    cases k with
    | zero =>
      simp only [RectangleCell.eval, edge_truncate_zero, cellMap_endpoint, cellMap_edge]
      cases b
      · exact (D.edge_source a).symm
      · exact (D.edge_target a).symm
    | succ k =>
      simp only [RectangleCell.eval, edge_truncate_succ, cellMap_edge]
      exact (Y.face_of_fixed (D.edge_fixed a) (show 1 ≤ k+1 by omega) b).symm
  | diagonal x =>
    cases k with
    | zero =>
      simp only [RectangleCell.eval, up_truncate_zero, cellMap_endpoint, cellMap_up]
      cases b
      · exact (D.diagonal.map x).property.1.symm
      · exact (D.diagonal.map x).property.2.symm
    | succ k =>
      simp only [RectangleCell.eval, up_truncate_succ, cellMap_up]
      cases b
      · exact congrArg Subtype.val (D.diagonal.map_source k x)
      · exact congrArg Subtype.val (D.diagonal.map_target k x)

lemma cellMap_composable (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) :
    Y.target k (D.cellMap x) = Y.source k (D.cellMap y) := by
  exact (D.cellMap_truncate k true x).symm.trans
    ((congrArg D.cellMap h).trans (D.cellMap_truncate k false y))

lemma cellMap_fixed (k : ℕ) (x : Table (K.{u} (n+1)))
    (h : truncate k false x = x) : Y.source k (D.cellMap x) = D.cellMap x := by
  exact (D.cellMap_truncate k false x).symm.trans (congrArg D.cellMap h)

lemma cellMap_comp_of_left_fixed (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) (hx : truncate k false x = x) :
    D.cellMap (DirectedComplex.Table.comp k x y h) = Y.join k (D.cellMap x) (D.cellMap y) := by
  change D.cellMap ((K (n+1)).nu.comp k x y h) = _
  rw [(K (n+1)).nu.comp_of_left_source_fixed k x y h hx,
    Y.join_left_unit k _ _ (D.cellMap_fixed k x hx) (D.cellMap_composable k x y h)]

lemma cellMap_comp_of_right_fixed (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) (hy : truncate k false y = y) :
    D.cellMap (DirectedComplex.Table.comp k x y h) = Y.join k (D.cellMap x) (D.cellMap y) := by
  change D.cellMap ((K (n+1)).nu.comp k x y h) = _
  rw [(K (n+1)).nu.comp_of_right_source_fixed k x y h hy,
    Y.join_right_unit k _ _ (D.cellMap_fixed k y hy) (D.cellMap_composable k x y h)]

lemma cellMap_comp_positive (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate (k+1) true x = truncate (k+1) false y) :
    D.cellMap (DirectedComplex.Table.comp (k+1) x y h) =
      Y.join (k+1) (D.cellMap x) (D.cellMap y) := by
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  obtain ⟨s,rfl⟩ := RectangleCell.eval_surjective n y
  have hm := (positive_matching_iff k r s).mp h
  cases r with
  | endpoint a x =>
    cases s with
    | endpoint b y =>
      obtain ⟨hab,hxy⟩ := RectangleCell.endpoint.inj hm
      subst b
      change truncate (k+1) true x = truncate (k+1) false y at hxy
      change D.cellMap (DirectedComplex.Table.comp (k+1) (atEnd a x) (atEnd a y) h) = _
      have hc : DirectedComplex.Table.comp (k+1) (atEnd a x) (atEnd a y) h =
          atEnd a (DirectedComplex.Table.comp (k+1) x y hxy) :=
        (((complex (n+1)).cylinderEndpoint a).table_comp (k+1) x y hxy h).symm
      rw [hc, cellMap_endpoint]
      simp only [RectangleCell.eval, cellMap_endpoint]
      change (D.ends a).map ((complex (n+1)).nu.comp (k+1) x y hxy) = _
      rw [(D.ends a).map_comp (k+1) x y hxy ((D.ends a).map_composable hxy),
        Y.join_eq (k+1) _ _ ((D.ends a).map_composable hxy)]
    | edge b => cases hm
    | diagonal y => cases hm
  | edge a =>
    cases s with
    | endpoint b y => cases hm
    | edge b =>
      have hab : a = b := RectangleCell.edge.inj hm
      subst b
      exact D.cellMap_comp_of_left_fixed (k+1) _ _ h (edge_truncate_succ n k a false)
    | diagonal y => cases hm
  | diagonal x =>
    cases s with
    | endpoint b y => cases hm
    | edge b => cases hm
    | diagonal y =>
      have hxy : truncate k true x = truncate k false y := RectangleCell.diagonal.inj hm
      change D.cellMap (DirectedComplex.Table.comp (k+1) (up x) (up y) h) = _
      rw [← up_comp x y hxy h, cellMap_up]
      simp only [RectangleCell.eval, cellMap_up]
      have hd := D.diagonal.map_comp k x y hxy (D.diagonal.map_composable hxy)
      have hd' := congrArg Subtype.val hd
      change _ = Y.comp (k+1) _ _ _ at hd'
      exact hd'.trans (Y.join_eq (k+1) _ _ _).symm

lemma cellMap_comp_zero (x y : Table (K.{u} (n+1)))
    (h : truncate 0 true x = truncate 0 false y) :
    D.cellMap (DirectedComplex.Table.comp 0 x y h) = Y.join 0 (D.cellMap x) (D.cellMap y) := by
  by_cases hx : truncate 0 false x = x
  · exact D.cellMap_comp_of_left_fixed 0 x y h hx
  by_cases hy : truncate 0 false y = y
  · exact D.cellMap_comp_of_right_fixed 0 x y h hy
  rcases nonobject_cases x hx with ⟨a,x,rfl⟩ | ⟨a,rfl⟩ | ⟨x,rfl⟩ <;>
    rcases nonobject_cases y hy with ⟨b,y,rfl⟩ | ⟨b,rfl⟩ | ⟨y,rfl⟩
  · simp only [atEnd_truncate, suspend_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.2
  · simp only [atEnd_truncate, suspend_truncate_zero, edge_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    obtain ⟨rfl,rfl⟩ := h
    rw [← up_endpoint_true, cellMap_up, D.right]
    simp
  · simp only [atEnd_truncate, suspend_truncate_zero, up_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.2
  · simp only [edge_truncate_zero, atEnd_truncate, suspend_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    obtain ⟨rfl,rfl⟩ := h
    rw [← up_endpoint_false, cellMap_up, D.left]
    simp
  · simp only [edge_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1
  · simp only [edge_truncate_zero, up_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1
  · simp only [up_truncate_zero, atEnd_truncate, suspend_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.2
  · simp only [up_truncate_zero, edge_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1
  · simp only [up_truncate_zero] at h
    have h := (atEnd_vertex_eq n _ _ _ _).mp h
    cases h.1

lemma cellMap_comp (k : ℕ) (x y : Table (K.{u} (n+1)))
    (h : truncate k true x = truncate k false y) :
    D.cellMap (DirectedComplex.Table.comp k x y h) = Y.join k (D.cellMap x) (D.cellMap y) := by
  cases k with
  | zero => exact D.cellMap_comp_zero x y h
  | succ k => exact D.cellMap_comp_positive k x y h

def lift : OmegaCategory.Functor (K.{u} (n+1)).nu Y where
  map := D.cellMap
  map_source k x := D.cellMap_truncate k false x
  map_target k x := D.cellMap_truncate k true x
  map_comp k x y h h' := (D.cellMap_comp k x y h).trans (Y.join_eq k _ _ h')

@[simp] lemma lift_endpoint (a : Bool) (x : Table (complex.{u} (n+1))) :
    D.lift.map (atEnd a x) = (D.ends a).map x := D.cellMap_endpoint a x
@[simp] lemma lift_edge (a : Bool) :
    D.lift.map (verticalTable (vertex n a)) = D.edge a := D.cellMap_edge a
@[simp] lemma lift_up (x : Table (K.{u} n)) :
    D.lift.map (up x) = (D.diagonal.map x).val := D.cellMap_up x

end RectangleDiagram
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

def extractDiagonal {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) :
    OmegaCategory.Functor (K.{u} n).nu
      (Y.homCategory (F.map (atEnd false (vertex n false)))
        (F.map (atEnd true (vertex n true)))) where
  map x := ⟨F.map (up x), by
    erw [← F.map_source, ← F.map_target]
    exact ⟨congrArg F.map (up_truncate_zero false x),
      congrArg F.map (up_truncate_zero true x)⟩⟩
  map_source k x := Subtype.ext (by
    change F.map (up (truncate k false x)) = Y.source (k+1) (F.map (up x))
    erw [up_truncate]; exact F.map_source _ _)
  map_target k x := Subtype.ext (by
    change F.map (up (truncate k true x)) = Y.target (k+1) (F.map (up x))
    erw [up_truncate]; exact F.map_target _ _)
  map_comp k x y h h' := Subtype.ext (by
    change F.map (up (DirectedComplex.Table.comp k x y h)) = Y.comp (k+1) _ _ _
    rw [up_comp x y h (up_composable h)]
    exact F.map_comp _ _ _ (up_composable h) (congrArg Subtype.val h'))

def rectangleDiagramOfFunctor {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) : RectangleDiagram.{u,v} n Y where
  ends a := OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu F
  edge a := F.map (verticalTable (vertex n a))
  edge_fixed a := by
    erw [← F.map_source]
    exact congrArg F.map (edge_truncate_succ n 0 a false)
  edge_source a := by
    erw [← F.map_source]
    exact congrArg F.map (edge_truncate_zero n a false)
  edge_target a := by
    erw [← F.map_target]
    exact congrArg F.map (edge_truncate_zero n a true)
  diagonal := extractDiagonal F
  left x := by
    change F.map (up (atEnd false x)) = _
    rw [up_endpoint_false]
    exact (F.map_comp 0 _ _ (up_endpoint_left_matching x) (F.map_composable (up_endpoint_left_matching x))).trans
      (Y.join_eq 0 _ _ _).symm
  right x := by
    change F.map (up (atEnd true x)) = _
    rw [up_endpoint_true]
    exact (F.map_comp 0 _ _ (up_endpoint_right_matching x) (F.map_composable (up_endpoint_right_matching x))).trans
      (Y.join_eq 0 _ _ _).symm

lemma functor_ext_rectangle {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (ends : ∀ a x, F.map (atEnd a x) = G.map (atEnd a x))
    (edge : ∀ a, F.map (verticalTable (vertex n a)) = G.map (verticalTable (vertex n a)))
    (diagonal : ∀ x, F.map (up x) = G.map (up x)) : F = G := by
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  cases r with
  | endpoint a x => exact ends a x
  | edge a => exact edge a
  | diagonal x => exact diagonal x

@[simp] lemma rectangleDiagramOfFunctor_lift {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) : (rectangleDiagramOfFunctor F).lift = F := by
  apply functor_ext_rectangle
  · intro a x; exact RectangleDiagram.lift_endpoint _ a x
  · intro a; exact RectangleDiagram.lift_edge _ a
  · intro x; exact RectangleDiagram.lift_up _ x

lemma RectangleDiagram.lift_unique {n : ℕ} {Y : OmegaCategory.{v}}
    (D : RectangleDiagram.{u,v} n Y) (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (ends : ∀ a x, F.map (atEnd a x) = (D.ends a).map x)
    (edge : ∀ a, F.map (verticalTable (vertex n a)) = D.edge a)
    (diagonal : ∀ x, F.map (up x) = (D.diagonal.map x).val) : F = D.lift := by
  apply functor_ext_rectangle
  · intro a x; exact (ends a x).trans (D.lift_endpoint a x).symm
  · intro a; exact (edge a).trans (D.lift_edge a).symm
  · intro x; exact (diagonal x).trans (D.lift_up x).symm

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
open CategoryTheory

def homCompose {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    (F : Functor X (Y.homCategory a b)) (G : Functor X (Y.homCategory b c)) :
    Functor X (Y.homCategory a c) where
  map x := ⟨Y.join 0 (F.map x).val (G.map x).val, by
    have h := (F.map x).property.2.trans (G.map x).property.1.symm
    exact ⟨(Y.join_source_le 0 0 _ _ le_rfl h).trans (F.map x).property.1,
      (Y.join_target_le 0 0 _ _ le_rfl h).trans (G.map x).property.2⟩⟩
  map_source k x := Subtype.ext (by
    have h := (F.map x).property.2.trans (G.map x).property.1.symm
    change Y.join 0 (F.map (X.source k x)).val (G.map (X.source k x)).val =
      Y.source (k+1) (Y.join 0 (F.map x).val (G.map x).val)
    rw [F.map_source, G.map_source, Y.join_source_gt (k+1) 0 _ _ (by omega) h]
    rfl)
  map_target k x := Subtype.ext (by
    have h := (F.map x).property.2.trans (G.map x).property.1.symm
    change Y.join 0 (F.map (X.target k x)).val (G.map (X.target k x)).val =
      Y.target (k+1) (Y.join 0 (F.map x).val (G.map x).val)
    rw [F.map_target, G.map_target, Y.join_target_gt (k+1) 0 _ _ (by omega) h]
    rfl)
  map_comp k x y h h' := Subtype.ext (by
    have hfx := F.map_composable h
    have hgx := G.map_composable h
    have h₁ := (F.map x).property.2.trans (G.map x).property.1.symm
    have h₂ := (F.map y).property.2.trans (G.map y).property.1.symm
    change Y.join 0 (F.map (X.comp k x y h)).val (G.map (X.comp k x y h)).val =
      Y.comp (k+1) _ _ _
    rw [F.map_comp _ _ _ h hfx, G.map_comp _ _ _ h hgx]
    change Y.join 0 (Y.comp (k+1) _ _ (congrArg Subtype.val hfx))
      (Y.comp (k+1) _ _ (congrArg Subtype.val hgx)) = Y.comp (k+1) _ _ _
    rw [← Y.join_eq (k+1) _ _ (congrArg Subtype.val hfx),
      ← Y.join_eq (k+1) _ _ (congrArg Subtype.val hgx)]
    exact (Y.join_interchange 0 (k+1) (by omega) _ _ _ _
      (congrArg Subtype.val hfx) (congrArg Subtype.val hgx) h₁ h₂).trans
      (Y.join_eq (k+1) _ _ _))

@[simp] lemma homCompose_map {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}} {a b c : Y.Cell}
    (F : Functor X (Y.homCategory a b)) (G : Functor X (Y.homCategory b c)) (x : X.Cell) :
    ((homCompose F G).map x).val = Y.join 0 (F.map x).val (G.map x).val := rfl

def constantAt (X : OmegaCategory.{u}) {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) : Functor X Y where
  map _ := a
  map_source k _ := (Y.source_fixed_upwards (Nat.zero_le k) ha).symm
  map_target k _ := (Y.target_eq_self_of_source_eq_self
    (Y.source_fixed_upwards (Nat.zero_le k) ha)).symm
  map_comp k _ _ _ h' := (Y.comp_of_left_source_fixed k a a h'
    (Y.source_fixed_upwards (Nat.zero_le _) ha)).symm

def constantHom (X : OmegaCategory.{u}) {Y : OmegaCategory.{v}} {a b : Y.Cell}
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = a) (ht : Y.target 0 f = b) :
    Functor X (Y.homCategory a b) := constantAt X ⟨f,hs,ht⟩ (Subtype.ext hf)

def homCast {X : OmegaCategory.{u}} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F : Functor X (Y.homCategory a b)) (hac : a = c) (hbd : b = d) :
    Functor X (Y.homCategory c d) where
  map x := ⟨(F.map x).val, (F.map x).property.1.trans hac, (F.map x).property.2.trans hbd⟩
  map_source k x := Subtype.ext (congrArg (fun z : (Y.homCategory a b).Cell => z.val) (F.map_source k x))
  map_target k x := Subtype.ext (congrArg (fun z : (Y.homCategory a b).Cell => z.val) (F.map_target k x))
  map_comp k x y h _ := Subtype.ext
    (congrArg (fun z : (Y.homCategory a b).Cell => z.val) (F.map_comp k x y h (F.map_composable h)))

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex

lemma globe_zero_unique (x : Table (complex.{u} 0)) : x = topTable 0 := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  have hp0 : p = 0 := by omega
  subst p
  rw [he, ← face_nu]
  exact (complex 0).nu.face_of_fixed (topTable_bounded 0) le_rfl a

lemma globe_one_cases (x : Table (complex.{u} 1)) :
    (∃ a, x = vertex 0 a) ∨ x = topTable 1 := by
  rcases globe_succ_cases 0 x with h | ⟨x,rfl⟩
  · exact Or.inl h
  · right
    rw [globe_zero_unique x, suspendTable_top]

def zeroCylinderMap : OmegaCategory.Functor (complex.{u} 1).nu (K.{u} 0).nu :=
  GlobeComplex.lift (verticalTable (topTable 0))
    (vertical_fixed _ (topTable_bounded 0))

@[simp] lemma zeroCylinderMap_top :
    zeroCylinderMap.{u}.map (topTable 1) = verticalTable (topTable 0) :=
  lift_top _ _

@[simp] lemma zeroCylinderMap_vertex (a : Bool) :
    zeroCylinderMap.{u}.map (vertex 0 a) = atEnd a (topTable 0) := by
  rw [vertex, ← face_nu]
  erw [zeroCylinderMap.map_face, zeroCylinderMap_top]
  have hf : (K.{u} 0).nu.face 0 a (verticalTable (topTable 0)) =
      truncate 0 a (verticalTable (topTable 0)) := by cases a <;> rfl
  rw [hf]
  apply DirectedComplex.Table.ext
  funext p b
  cases p with
  | zero => cases a <;> simp [truncate_row, verticalTable, verticalRow,
      atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap, topTable, topRow_eq]
  | succ p => cases a <;> simp [truncate_row, atEnd, Hom.table,
      cylinderEndpoint, cylinderEndpointMap, topTable, topRow_gt _ _ _ (show 0 < p+1 by omega)] <;> rfl

lemma zeroCylinderMap_bijective : Function.Bijective zeroCylinderMap.{u}.map := by
  constructor
  · intro s t h
    have hs := congrArg (fun x => intervalLabel x false) h
    have ht := congrArg (fun x => intervalLabel x true) h
    rcases globe_one_cases s with ⟨a,rfl⟩ | rfl <;>
      rcases globe_one_cases t with ⟨b,rfl⟩ | rfl
    · simp only [zeroCylinderMap_vertex, intervalLabel_end] at hs ht
      have hab : a = b := by cases a <;> cases b <;> simp_all
      rw [hab]
    · exfalso
      cases a
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, zero_ne_one] at ht
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, one_ne_zero] at hs
    · exfalso
      cases b
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, one_ne_zero] at ht
      · simp only [zeroCylinderMap_vertex, zeroCylinderMap_top, intervalLabel_end,
          intervalLabel_vertical, Bool.false_eq_true, ite_false, ite_true, zero_ne_one] at hs
    · rfl
  · intro t
    rcases table_zero_cases t with ⟨a,he⟩ | he
    · exact ⟨vertex 0 a, (zeroCylinderMap_vertex a).trans
        ((congrArg (atEnd a) (globe_zero_unique (project t))).symm.trans he.symm)⟩
    · exact ⟨topTable 1, zeroCylinderMap_top.trans he.symm⟩

def zeroCylinderIso : (complex.{u} 1).nu ≅ (K.{u} 0).nu :=
  OmegaCategory.isoOfBijective zeroCylinderMap zeroCylinderMap_bijective

def zeroCylinderLift {Y : OmegaCategory.{v}} (y : Y.Cell) (hy : Y.source 1 y = y) :
    OmegaCategory.Functor (K.{u} 0).nu Y :=
  OmegaCategory.Functor.comp zeroCylinderIso.inv (GlobeComplex.lift y hy)

@[simp] lemma zeroCylinderLift_vertical {Y : OmegaCategory.{v}} (y : Y.Cell)
    (hy : Y.source 1 y = y) :
    (zeroCylinderLift.{u,v} y hy).map (verticalTable (topTable 0)) = y := by
  have hi : zeroCylinderIso.{u}.inv.map (verticalTable (topTable 0)) = topTable 1 := by
    rw [← zeroCylinderMap_top]
    exact congrArg (fun F : OmegaCategory.Functor (complex 1).nu (complex 1).nu =>
      F.map (topTable 1)) zeroCylinderIso.hom_inv_id
  change (GlobeComplex.lift y hy).map _ = y
  rw [hi, lift_top]

@[simp] lemma zeroCylinderLift_endpoint {Y : OmegaCategory.{v}} (y : Y.Cell)
    (hy : Y.source 1 y = y) (a : Bool) (x : Table (complex.{u} 0)) :
    (zeroCylinderLift y hy).map (atEnd a x) = Y.face 0 a y := by
  rw [globe_zero_unique x]
  have hi : zeroCylinderIso.{u}.inv.map (atEnd a (topTable 0)) = vertex 0 a := by
    rw [← zeroCylinderMap_vertex]
    exact congrArg (fun F : OmegaCategory.Functor (complex 1).nu (complex 1).nu =>
      F.map (vertex 0 a)) zeroCylinderIso.hom_inv_id
  change (GlobeComplex.lift y hy).map _ = _
  rw [hi]
  rw [vertex, ← face_nu]
  erw [(GlobeComplex.lift y hy).map_face, lift_top]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def IntervalMatching {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) : Prop :=
  ∀ x, F.map (atEnd true x) = G.map (atEnd false x)

structure IntervalComposition (n : ℕ) where
  compose : ∀ {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y), IntervalMatching F G →
    OmegaCategory.Functor (K.{u} n).nu Y
  endpoint : ∀ {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (a : Bool) x,
    (compose F G h).map (atEnd a x) = if a then G.map (atEnd true x) else F.map (atEnd false x)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}}
    (D E : RectangleDiagram.{u,v} n Y)
    (h : ∀ x, (D.ends true).map x = (E.ends false).map x)

include h in
lemma seam_edge (a : Bool) : Y.target 0 (D.edge a) = Y.source 0 (E.edge a) :=
  (D.edge_target a).trans ((h _).trans (E.edge_source a).symm)

lemma edge_end_matching (D : RectangleDiagram.{u,v} n Y) (x : Table (complex.{u} n)) :
    Y.target 0 (D.edge false) = Y.source 0 ((D.ends true).map (suspendTable x)) := by
  erw [D.edge_target, ← (D.ends true).map_source]
  exact congrArg (D.ends true).map (suspend_truncate_zero false x).symm

lemma end_edge_matching (D : RectangleDiagram.{u,v} n Y) (x : Table (complex.{u} n)) :
    Y.target 0 ((D.ends false).map (suspendTable x)) = Y.source 0 (D.edge true) := by
  erw [D.edge_source, ← (D.ends false).map_target]
  exact congrArg (D.ends false).map (suspend_truncate_zero true x)

def concatDiagonalOne : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose (constantHom (K n).nu (D.edge false) (D.edge_fixed false)
    (D.edge_source false) ((D.edge_target false).trans (h _))) E.diagonal

def concatDiagonalTwo : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) :=
  homCompose D.diagonal (constantHom (K n).nu (E.edge true) (E.edge_fixed true)
    ((E.edge_source true).trans (h _).symm) (E.edge_target true))

lemma concatDiagonal_matching : IntervalMatching (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) := by
  intro x
  apply Subtype.ext
  change Y.join 0 (D.edge false) (E.diagonal.map (atEnd true x)).val =
    Y.join 0 (D.diagonal.map (atEnd false x)).val (E.edge true)
  erw [E.right, D.left, h]
  exact (Y.join_assoc 0 _ _ _ (by
    erw [← h]
    exact D.edge_end_matching x) (E.end_edge_matching x)).symm

def concat (I : IntervalComposition.{u,v} n) : RectangleDiagram.{u,v} n Y where
  ends a := if a then E.ends true else D.ends false
  edge a := Y.join 0 (D.edge a) (E.edge a)
  edge_fixed a := by
    rw [Y.join_source_gt 1 0 _ _ (by omega) (D.seam_edge E h a), D.edge_fixed, E.edge_fixed]
  edge_source a := by
    exact (Y.join_source_le 0 0 _ _ le_rfl (D.seam_edge E h a)).trans (D.edge_source a)
  edge_target a := by
    exact (Y.join_target_le 0 0 _ _ le_rfl (D.seam_edge E h a)).trans (E.edge_target a)
  diagonal := I.compose (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h)
  left x := by
    have he := congrArg Subtype.val (I.endpoint (D.concatDiagonalOne E h)
      (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h) false x)
    simp only [Bool.false_eq_true, ite_false] at he
    change _ = Y.join 0 (Y.join 0 (D.edge false) (E.edge false)) ((E.ends true).map (suspendTable x))
    rw [he]
    change Y.join 0 (D.edge false) (E.diagonal.map (atEnd false x)).val = _
    rw [E.left]
    exact (Y.join_assoc 0 _ _ _ (D.seam_edge E h false) (E.edge_end_matching x)).symm
  right x := by
    have he := congrArg Subtype.val (I.endpoint (D.concatDiagonalOne E h)
      (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h) true x)
    simp only [ite_true] at he
    change _ = Y.join 0 ((D.ends false).map (suspendTable x)) (Y.join 0 (D.edge true) (E.edge true))
    rw [he]
    change Y.join 0 (D.diagonal.map (atEnd true x)).val (E.edge true) = _
    rw [D.right]
    exact Y.join_assoc 0 _ _ _ (D.end_edge_matching x) (D.seam_edge E h true)

end RectangleDiagram

namespace IntervalComposition

def zero : IntervalComposition.{u,v} 0 where
  compose {Y} F G h :=
    zeroCylinderLift (Y.join 0 (F.map (verticalTable (topTable 0))) (G.map (verticalTable (topTable 0)))) (by
      have hm : Y.target 0 (F.map (verticalTable (topTable 0))) =
          Y.source 0 (G.map (verticalTable (topTable 0))) := by
        erw [← F.map_target, ← G.map_source]
        have ht := zeroCylinderMap.map_target 0 (topTable 1)
        have hs := zeroCylinderMap.map_source 0 (topTable 1)
        change zeroCylinderMap.map (vertex 0 true) = _ at ht
        change zeroCylinderMap.map (vertex 0 false) = _ at hs
        rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at ht hs
        rw [← ht, ← hs]
        exact h _
      erw [Y.join_source_gt 1 0 _ _ (by omega) hm, ← F.map_source, ← G.map_source]
      change Y.join 0 (F.map (truncate 1 false (verticalTable (topTable 0))))
        (G.map (truncate 1 false (verticalTable (topTable 0)))) = _
      rw [vertical_fixed _ (topTable_bounded 0)])
  endpoint {Y} F G h a x := by
    rw [zeroCylinderLift_endpoint]
    have ht := zeroCylinderMap.map_target 0 (topTable 1)
    have hs := zeroCylinderMap.map_source 0 (topTable 1)
    change zeroCylinderMap.map (vertex 0 true) = _ at ht
    change zeroCylinderMap.map (vertex 0 false) = _ at hs
    rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at ht hs
    have hm : Y.target 0 (F.map (verticalTable (topTable 0))) =
        Y.source 0 (G.map (verticalTable (topTable 0))) := by
      erw [← F.map_target, ← G.map_source]
      rw [← ht, ← hs]; exact h _
    rw [globe_zero_unique x]
    cases a
    · change Y.source 0 _ = _
      erw [Y.join_source_le 0 0 _ _ le_rfl hm, ← F.map_source]
      exact congrArg F.map hs.symm
    · change Y.target 0 _ = _
      erw [Y.join_target_le 0 0 _ _ le_rfl hm, ← G.map_target]
      exact congrArg G.map ht.symm

def succ {n : ℕ} (I : IntervalComposition.{u,v} n) : IntervalComposition.{u,v} (n+1) where
  compose F G h := ((rectangleDiagramOfFunctor F).concat (rectangleDiagramOfFunctor G) h I).lift
  endpoint F G h a x := by
    rw [RectangleDiagram.lift_endpoint]
    cases a <;> rfl

end IntervalComposition

def intervalComposition : (n : ℕ) → IntervalComposition.{u,v} n
  | 0 => IntervalComposition.zero
  | n+1 => (intervalComposition n).succ

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}

def map (D : RectangleDiagram.{u,v} n Y) (P : OmegaCategory.Functor Y Z) :
    RectangleDiagram.{u,w} n Z where
  ends a := OmegaCategory.Functor.comp (D.ends a) P
  edge a := P.map (D.edge a)
  edge_fixed a := by rw [← P.map_source, D.edge_fixed]
  edge_source a := by rw [← P.map_source, D.edge_source]; rfl
  edge_target a := by rw [← P.map_target, D.edge_target]; rfl
  diagonal := OmegaCategory.Functor.comp D.diagonal
    (P.homMap ((D.ends false).map (vertex n false)) ((D.ends true).map (vertex n true)))
  left x := by
    change P.map (D.diagonal.map (atEnd false x)).val = _
    rw [D.left, P.map_join _ _ _ (D.edge_end_matching x)]
    rfl
  right x := by
    change P.map (D.diagonal.map (atEnd true x)).val = _
    rw [D.right, P.map_join _ _ _ (D.end_edge_matching x)]
    rfl

lemma map_ofFunctor (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (P : OmegaCategory.Functor Y Z) :
    (rectangleDiagramOfFunctor F).map P = rectangleDiagramOfFunctor (OmegaCategory.Functor.comp F P) := rfl

lemma lift_map (D : RectangleDiagram.{u,v} n Y) (P : OmegaCategory.Functor Y Z) :
    (D.map P).lift = OmegaCategory.Functor.comp D.lift P := by
  apply functor_ext_rectangle
  · intro a x; rw [lift_endpoint]; exact congrArg P.map (D.lift_endpoint a x).symm
  · intro a; rw [lift_edge]; exact congrArg P.map (D.lift_edge a).symm
  · intro x; rw [lift_up]; exact congrArg P.map (D.lift_up x).symm

variable (D E : RectangleDiagram.{u,v} n Y)
    (h : ∀ x, (D.ends true).map x = (E.ends false).map x) (P : OmegaCategory.Functor Y Z)

lemma map_concatDiagonalOne :
    OmegaCategory.Functor.comp (D.concatDiagonalOne E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).concatDiagonalOne (E.map P) (fun x => congrArg P.map (h x)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 (D.edge false) (E.diagonal.map x).val) =
    Z.join 0 (P.map (D.edge false)) (P.map (E.diagonal.map x).val)
  exact P.map_join 0 _ _ ((D.edge_target false).trans ((h _).trans (E.diagonal.map x).property.1.symm))

lemma map_concatDiagonalTwo :
    OmegaCategory.Functor.comp (D.concatDiagonalTwo E h)
      (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true))) =
    (D.map P).concatDiagonalTwo (E.map P) (fun x => congrArg P.map (h x)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change P.map (Y.join 0 (D.diagonal.map x).val (E.edge true)) =
    Z.join 0 (P.map (D.diagonal.map x).val) (P.map (E.edge true))
  exact P.map_join 0 _ _ ((D.diagonal.map x).property.2.trans ((h _).trans (E.edge_source true).symm))

end RectangleDiagram

abbrev concatInterval {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) :=
  (intervalComposition n).compose F G h

@[simp] lemma concatInterval_endpoint {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (a : Bool) x :
    (concatInterval F G h).map (atEnd a x) = if a then G.map (atEnd true x) else F.map (atEnd false x) :=
  (intervalComposition n).endpoint F G h a x

@[simp] lemma concatInterval_zero_vertical {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} 0).nu Y) (h : IntervalMatching F G) :
    (concatInterval F G h).map (verticalTable (topTable 0)) =
      Y.join 0 (F.map (verticalTable (topTable 0))) (G.map (verticalTable (topTable 0))) :=
  zeroCylinderLift_vertical _ _

@[simp] lemma concatInterval_succ_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : IntervalMatching F G) (a : Bool) :
    (concatInterval F G h).map (verticalTable (vertex n a)) =
      Y.join 0 (F.map (verticalTable (vertex n a))) (G.map (verticalTable (vertex n a))) :=
  RectangleDiagram.lift_edge _ a

lemma concatInterval_succ_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : IntervalMatching F G) (x : Table (K.{u} n)) :
    (concatInterval F G h).map (up x) =
      ((concatInterval ((rectangleDiagramOfFunctor F).concatDiagonalOne (rectangleDiagramOfFunctor G) h)
        ((rectangleDiagramOfFunctor F).concatDiagonalTwo (rectangleDiagramOfFunctor G) h)
        ((rectangleDiagramOfFunctor F).concatDiagonal_matching (rectangleDiagramOfFunctor G) h)).map x).val :=
  RectangleDiagram.lift_up _ x

lemma zero_interval_seam {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} 0).nu Y) (h : IntervalMatching F G) :
    Y.target 0 (F.map (verticalTable (topTable 0))) = Y.source 0 (G.map (verticalTable (topTable 0))) := by
  erw [← F.map_target, ← G.map_source]
  have ht := zeroCylinderMap.map_target 0 (topTable 1)
  have hs := zeroCylinderMap.map_source 0 (topTable 1)
  change zeroCylinderMap.map (vertex 0 true) = _ at ht
  change zeroCylinderMap.map (vertex 0 false) = _ at hs
  rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at ht hs
  rw [← ht, ← hs]
  exact h _

lemma concatInterval_natural (n : ℕ) {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G)
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (concatInterval F G h) P =
      concatInterval (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P)
        (fun x => congrArg P.map (h x)) := by
  induction n generalizing Y Z with
  | zero =>
    apply OmegaCategory.Functor.ext
    funext x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he]
      change P.map ((concatInterval F G h).map (atEnd a (project x))) = _
      erw [concatInterval_endpoint, concatInterval_endpoint]
      cases a <;> rfl
    · rw [he]
      change P.map ((concatInterval F G h).map (verticalTable (topTable 0))) = _
      erw [concatInterval_zero_vertical, concatInterval_zero_vertical]
      exact P.map_join 0 _ _ (zero_interval_seam F G h)
  | succ n ih =>
    apply functor_ext_rectangle
    · intro a x
      change P.map ((concatInterval F G h).map (atEnd a x)) = _
      erw [concatInterval_endpoint, concatInterval_endpoint]
      cases a <;> rfl
    · intro a
      change P.map ((concatInterval F G h).map (verticalTable (vertex n a))) = _
      erw [concatInterval_succ_edge, concatInterval_succ_edge]
      exact P.map_join 0 _ _ ((rectangleDiagramOfFunctor F).seam_edge (rectangleDiagramOfFunctor G) h a)
    · intro x
      change P.map ((concatInterval F G h).map (up x)) = _
      erw [concatInterval_succ_up, concatInterval_succ_up]
      let D := rectangleDiagramOfFunctor F
      let E := rectangleDiagramOfFunctor G
      have hh := ih (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h)
        (D.concatDiagonal_matching E h)
        (P.homMap ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
      simp only [D.map_concatDiagonalOne E h P, D.map_concatDiagonalTwo E h P] at hh
      exact congrArg (fun U => (U.map x).val) hh

end Thomason.GrayRecursive

end

end OAI
