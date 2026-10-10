import Mathlib
import OAI.CategoryTheory.Thomason.CylinderAssociativity

namespace OAI

/-! Stationary Cylinders. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def endGlobe {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) :
    OmegaCategory.Functor (complex.{u} n).nu Y :=
  OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F

@[simp] lemma endGlobe_map {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) (x : Table (complex.{u} n)) :
    (endGlobe F a).map x = F.map (atEnd a x) := rfl

lemma stationary_left_matching {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    IntervalMatching (constantInterval (endGlobe F false)) F := by
  intro x
  exact constantInterval_endpoint _ _ _

lemma stationary_right_matching {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    IntervalMatching F (constantInterval (endGlobe F true)) := by
  intro x
  exact (constantInterval_endpoint (endGlobe F true) false x).symm

def IntervalUnits (n : ℕ) : Prop :=
  ∀ {Y : OmegaCategory.{v}} (F : OmegaCategory.Functor (K.{u} n).nu Y),
    concatInterval (constantInterval (endGlobe F false)) F (stationary_left_matching F) = F ∧
    concatInterval F (constantInterval (endGlobe F true)) (stationary_right_matching F) = F

lemma zero_vertical_source {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) :
    Y.source 0 (F.map (verticalTable (topTable 0))) = F.map (atEnd false (topTable 0)) := by
  have h := zeroCylinderMap.map_source 0 (topTable.{u} 1)
  change zeroCylinderMap.map (vertex 0 false) = _ at h
  rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at h
  exact (F.map_source _ _).symm.trans (congrArg F.map h.symm)
lemma zero_vertical_target {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} 0).nu Y) :
    Y.target 0 (F.map (verticalTable (topTable 0))) = F.map (atEnd true (topTable 0)) := by
  have h := zeroCylinderMap.map_target 0 (topTable.{u} 1)
  change zeroCylinderMap.map (vertex 0 true) = _ at h
  rw [zeroCylinderMap_vertex, zeroCylinderMap_top] at h
  exact (F.map_target _ _).symm.trans (congrArg F.map h.symm)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{v}} (D : RectangleDiagram.{u,v} n Y)
lemma vertex_fixed (a b : Bool) :
    Y.source 0 ((D.ends a).map (vertex n b)) = (D.ends a).map (vertex n b) := by
  erw [← (D.ends a).map_source]
  exact congrArg (D.ends a).map (vertex_truncate n 0 b false)

lemma vertex_target_fixed (a b : Bool) :
    Y.target 0 ((D.ends a).map (vertex n b)) = (D.ends a).map (vertex n b) :=
  Y.target_eq_self_of_source_eq_self (D.vertex_fixed a b)
end RectangleDiagram

lemma concatInterval_units (n : ℕ) : IntervalUnits.{u,v} n := by
  induction n with
  | zero =>
    intro Y F
    constructor
    · apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · rw [he, concatInterval_endpoint]
        cases a <;> simp
      · rw [he, concatInterval_zero_vertical, constantInterval_map, project_zero_vertical,
          endGlobe_map, ← zero_vertical_source]
        exact Y.join_left_unit 0 _ _ (Y.source_source_self 0 _) (Y.target_source_self 0 _)
    · apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · rw [he, concatInterval_endpoint]
        cases a <;> simp
      · rw [he, concatInterval_zero_vertical, constantInterval_map, project_zero_vertical,
          endGlobe_map, ← zero_vertical_target]
        exact Y.join_right_unit 0 _ _ (Y.source_target_self 0 _) (Y.source_target_self 0 _).symm
  | succ n ih =>
    intro Y F
    let D := rectangleDiagramOfFunctor F
    constructor
    · apply functor_ext_rectangle
      · intro a x
        rw [concatInterval_endpoint]
        cases a <;> simp
      · intro a
        rw [concatInterval_succ_edge, constantInterval_edge]
        change Y.join 0 ((D.ends false).map (vertex n a)) (D.edge a) = D.edge a
        apply Y.join_left_unit 0 _ _ (D.vertex_fixed false a)
        rw [D.vertex_target_fixed]
        exact (D.edge_source a).symm
      · intro x
        rw [concatInterval_succ_up]
        let E := rectangleDiagramOfFunctor (constantInterval (endGlobe F false))
        have hA (t : Table (K.{u} n)) :
            ((E.concatDiagonalOne D (stationary_left_matching F)).map t).val = (D.diagonal.map t).val := by
          change Y.join 0 ((constantInterval (endGlobe F false)).map (verticalTable (vertex n false)))
            (D.diagonal.map t).val = _
          rw [constantInterval_edge]
          change Y.join 0 ((D.ends false).map (vertex n false)) (D.diagonal.map t).val = _
          apply Y.join_left_unit 0 _ _ (D.vertex_fixed false false)
          rw [D.vertex_target_fixed]
          exact (D.diagonal.map t).property.1.symm
        have hB (t : Table (K.{u} n)) :
            ((E.concatDiagonalTwo D (stationary_left_matching F)).map t).val =
              ((constantInterval (endGlobe D.diagonal true)).map t).val := by
          change Y.join 0 ((constantInterval (endGlobe F false)).map (up t)) (D.edge true) =
            (D.diagonal.map (atEnd true (project t))).val
          rw [constantInterval_up, D.right]
          rfl
        have he := concatInterval_val_congr
          (E.concatDiagonalOne D (stationary_left_matching F))
          (E.concatDiagonalTwo D (stationary_left_matching F))
          (E.concatDiagonal_matching D (stationary_left_matching F))
          D.diagonal (constantInterval (endGlobe D.diagonal true))
          (stationary_right_matching D.diagonal) hA hB x
        exact he.trans (congrArg (fun A => (A.map x).val) (ih D.diagonal).2)
    · apply functor_ext_rectangle
      · intro a x
        rw [concatInterval_endpoint]
        cases a <;> simp
      · intro a
        rw [concatInterval_succ_edge, constantInterval_edge]
        change Y.join 0 (D.edge a) ((D.ends true).map (vertex n a)) = D.edge a
        exact Y.join_right_unit 0 _ _ (D.vertex_fixed true a)
          ((D.edge_target a).trans (D.vertex_fixed true a).symm)
      · intro x
        rw [concatInterval_succ_up]
        let E := rectangleDiagramOfFunctor (constantInterval (endGlobe F true))
        have hA (t : Table (K.{u} n)) :
            ((D.concatDiagonalOne E (stationary_right_matching F)).map t).val =
              ((constantInterval (endGlobe D.diagonal false)).map t).val := by
          change Y.join 0 (D.edge false) ((constantInterval (endGlobe F true)).map (up t)) =
            (D.diagonal.map (atEnd false (project t))).val
          rw [constantInterval_up, D.left]
          rfl
        have hB (t : Table (K.{u} n)) :
            ((D.concatDiagonalTwo E (stationary_right_matching F)).map t).val = (D.diagonal.map t).val := by
          change Y.join 0 (D.diagonal.map t).val
            ((constantInterval (endGlobe F true)).map (verticalTable (vertex n true))) = _
          rw [constantInterval_edge]
          change Y.join 0 (D.diagonal.map t).val ((D.ends true).map (vertex n true)) = _
          exact Y.join_right_unit 0 _ _ (D.vertex_fixed true true)
            ((D.diagonal.map t).property.2.trans (D.vertex_fixed true true).symm)
        have he := concatInterval_val_congr
          (D.concatDiagonalOne E (stationary_right_matching F))
          (D.concatDiagonalTwo E (stationary_right_matching F))
          (D.concatDiagonal_matching E (stationary_right_matching F))
          (constantInterval (endGlobe D.diagonal false)) D.diagonal
          (stationary_left_matching D.diagonal) hA hB x
        exact he.trans (congrArg (fun A => (A.map x).val) (ih D.diagonal).1)

lemma concatInterval_left_unit {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    concatInterval (constantInterval (endGlobe F false)) F (stationary_left_matching F) = F :=
  (concatInterval_units n F).1
lemma concatInterval_right_unit {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    concatInterval F (constantInterval (endGlobe F true)) (stationary_right_matching F) = F :=
  (concatInterval_units n F).2
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma concatInterval_homCompose_stationary_left {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (P : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : IntervalMatching F G)
    (h' : IntervalMatching (homCompose (constantInterval P) F) (homCompose (constantInterval P) G)) :
    concatInterval (homCompose (constantInterval P) F) (homCompose (constantInterval P) G) h' =
      homCompose (constantInterval P) (concatInterval F G h) := by
  have e := concatInterval_homCompose (constantInterval P) (constantInterval P)
    (constantInterval_matching P) F G h
  exact e.trans (congrArg (fun A => homCompose A (concatInterval F G h)) (concatInterval_constant n P))

lemma concatInterval_homCompose_stationary_right {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (P : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory b c))
    (h' : IntervalMatching (homCompose F (constantInterval P)) (homCompose G (constantInterval P))) :
    concatInterval (homCompose F (constantInterval P)) (homCompose G (constantInterval P)) h' =
      homCompose (concatInterval F G h) (constantInterval P) := by
  have e := concatInterval_homCompose F G h (constantInterval P) (constantInterval P)
    (constantInterval_matching P)
  exact e.trans (congrArg (fun B => homCompose (concatInterval F G h) B) (concatInterval_constant n P))

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S : RectangleDiagram.{u,u} n Y) (h : D.edge true = E.edge false) (i : E.edge true = S.edge false)

namespace HorizontalAssociativity

def beforeGlobe : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends false).map (vertex n false))) :=
  homCast (globeHomMap (D.ends false)) rfl (D.horizontal_seam E h false)

def suffix : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory ((E.ends true).map (vertex n true)) ((S.ends true).map (vertex n true))) :=
  homCast (globeHomMap (S.ends true)) (E.horizontal_seam S i true).symm rfl

def A := homCompose (D.horizontalDiagonalOne E h) (constantInterval (suffix E S i))
def B := homCompose (D.horizontalDiagonalTwo E h) (constantInterval (suffix E S i))
def C := homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalTwo S i)

lemma B_map (x : Table (K.{u} n)) :
    ((B D E S h i).map x).val =
      ((homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalOne S i)).map x).val := by
  change Y.join 0 (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val)
    ((S.ends true).map (suspendTable (project x))) =
      Y.join 0 ((D.ends false).map (suspendTable (project x)))
        (Y.join 0 (E.diagonal.map x).val ((S.ends true).map (suspendTable (project x))))
  apply Y.join_assoc 0
  · erw [← (D.ends false).map_target]
    change (D.ends false).map (truncate 0 true (suspendTable (project x))) = _
    rw [suspend_truncate_zero, D.horizontal_seam E h]
    exact (E.diagonal.map x).property.1.symm
  · erw [← (S.ends true).map_source]
    change _ = (S.ends true).map (truncate 0 false (suspendTable (project x)))
    rw [suspend_truncate_zero, ← E.horizontal_seam S i]
    exact (E.diagonal.map x).property.2

lemma AB : IntervalMatching (A D E S h i) (B D E S h i) := by
  intro x
  apply Subtype.ext
  change Y.join 0 ((D.horizontalDiagonalOne E h).map (atEnd true x)).val
    ((constantInterval (suffix E S i)).map (atEnd true x)).val =
      Y.join 0 ((D.horizontalDiagonalTwo E h).map (atEnd false x)).val
        ((constantInterval (suffix E S i)).map (atEnd false x)).val
  rw [D.horizontalDiagonal_matching E h x, constantInterval_endpoint, constantInterval_endpoint]

lemma BC : IntervalMatching (B D E S h i) (C D E S h i) := by
  intro x
  apply Subtype.ext
  rw [B_map]
  change Y.join 0 ((constantInterval (beforeGlobe D E h)).map (atEnd true x)).val
    ((E.horizontalDiagonalOne S i).map (atEnd true x)).val =
      Y.join 0 ((constantInterval (beforeGlobe D E h)).map (atEnd false x)).val
        ((E.horizontalDiagonalTwo S i).map (atEnd false x)).val
  rw [E.horizontalDiagonal_matching S i x, constantInterval_endpoint, constantInterval_endpoint]

lemma left_one_map (x : Table (K.{u} n)) :
    (((D.horizontal E h).horizontalDiagonalOne S i).map x).val =
      ((concatInterval (A D E S h i) (B D E S h i) (AB D E S h i)).map x).val := by
  have he := concatInterval_homCompose_stationary_right
    (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h) (D.horizontalDiagonal_matching E h)
    (suffix E S i) (AB D E S h i)
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma left_two_map (x : Table (K.{u} n)) :
    (((D.horizontal E h).horizontalDiagonalTwo S i).map x).val = ((C D E S h i).map x).val := by
  erw [horizontalDiagonalTwo_map]
  simp only [horizontal, globeHorizontal_suspend]
  change Y.join 0 (Y.join 0 ((D.ends false).map (suspendTable (project x)))
    ((E.ends false).map (suspendTable (project x)))) (S.diagonal.map x).val =
      Y.join 0 ((D.ends false).map (suspendTable (project x)))
        (Y.join 0 ((E.ends false).map (suspendTable (project x))) (S.diagonal.map x).val)
  apply Y.join_assoc 0 _ _ _ (D.horizontal_source_match E h (project x) false)
  erw [← (E.ends false).map_target]
  change (E.ends false).map (truncate 0 true (suspendTable (project x))) = _
  rw [suspend_truncate_zero, E.horizontal_seam S i false]
  exact (S.diagonal.map x).property.1.symm

lemma right_one_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalOne (E.horizontal S i) h).map x).val = ((A D E S h i).map x).val := by
  erw [horizontalDiagonalOne_map]
  simp only [horizontal, globeHorizontal_suspend]
  change Y.join 0 (D.diagonal.map x).val
    (Y.join 0 ((E.ends true).map (suspendTable (project x))) ((S.ends true).map (suspendTable (project x)))) =
      Y.join 0 (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x))))
        ((S.ends true).map (suspendTable (project x)))
  symm
  apply Y.join_assoc 0 _ _ _ _ (E.horizontal_source_match S i (project x) true)
  erw [← (E.ends true).map_source]
  change _ = (E.ends true).map (truncate 0 false (suspendTable (project x)))
  rw [suspend_truncate_zero, ← D.horizontal_seam E h true]
  exact (D.diagonal.map x).property.2

lemma right_two_map (x : Table (K.{u} n)) :
    ((D.horizontalDiagonalTwo (E.horizontal S i) h).map x).val =
      ((concatInterval (B D E S h i) (C D E S h i) (BC D E S h i)).map x).val := by
  have hb : B D E S h i = homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalOne S i) :=
    OmegaCategory.Functor.ext (funext (fun x => Subtype.ext (B_map D E S h i x)))
  have hm : IntervalMatching
      (homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalOne S i))
      (homCompose (constantInterval (beforeGlobe D E h)) (E.horizontalDiagonalTwo S i)) := by
    simpa only [C, ← hb] using BC D E S h i
  have he := concatInterval_homCompose_stationary_left (beforeGlobe D E h)
    (E.horizontalDiagonalOne S i) (E.horizontalDiagonalTwo S i) (E.horizontalDiagonal_matching S i) hm
  simp only [← hb] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

end HorizontalAssociativity

lemma horizontal_associative :
    (D.horizontal E h).horizontal S i = D.horizontal (E.horizontal S i) h := by
  apply RectangleDiagram.ext
  · funext a
    apply GlobeComplex.functor_ext
    simp only [horizontal, globeHorizontal, lift_top]
    exact Y.join_assoc 0 _ _ _ (globe_horizontal_match _ _ (D.horizontal_seam E h a))
      (globe_horizontal_match _ _ (E.horizontal_seam S i a))
  · funext a
    cases a <;> rfl
  · intro x
    open HorizontalAssociativity in
    have hl := concatInterval_val_congr
      ((D.horizontal E h).horizontalDiagonalOne S i)
      ((D.horizontal E h).horizontalDiagonalTwo S i)
      ((D.horizontal E h).horizontalDiagonal_matching S i)
      (concatInterval (A D E S h i) (B D E S h i) (AB D E S h i))
      (C D E S h i) ((AB D E S h i).concat_left (BC D E S h i))
      (left_one_map D E S h i) (left_two_map D E S h i) x
    open HorizontalAssociativity in
    have hr := concatInterval_val_congr
      (D.horizontalDiagonalOne (E.horizontal S i) h)
      (D.horizontalDiagonalTwo (E.horizontal S i) h)
      (D.horizontalDiagonal_matching (E.horizontal S i) h)
      (A D E S h i)
      (concatInterval (B D E S h i) (C D E S h i) (BC D E S h i))
      ((AB D E S h i).concat_right (BC D E S h i))
      (right_one_map D E S h i) (right_two_map D E S h i) x
    open HorizontalAssociativity in
    have he := concatInterval_associative n (A D E S h i) (B D E S h i) (C D E S h i)
      (AB D E S h i) (BC D E S h i)
    exact hl.trans ((congrArg (fun Q => (Q.map x).val) he).trans hr.symm)

end RectangleDiagram

lemma horizontalCylinder_associative {n : ℕ} {Y : OmegaCategory.{u}}
    (F G H : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (i : G.map (verticalTable (vertex n true)) = H.map (verticalTable (vertex n false)))
    (h' : (horizontalCylinder F G h).map (verticalTable (vertex n true)) = H.map (verticalTable (vertex n false)))
    (i' : F.map (verticalTable (vertex n true)) = (horizontalCylinder G H i).map (verticalTable (vertex n false))) :
    horizontalCylinder (horizontalCylinder F G h) H h' = horizontalCylinder F (horizontalCylinder G H i) i' := by
  unfold horizontalCylinder
  simp only [RectangleDiagram.ofFunctor_lift]
  exact congrArg RectangleDiagram.lift
    ((rectangleDiagramOfFunctor F).horizontal_associative (rectangleDiagramOfFunctor G)
      (rectangleDiagramOfFunctor H) h i)
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma pasteCylinder_val_congr {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d)) (h' : FaceMatching k F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) (x : Table (K.{u} n)) :
    ((pasteCylinder hk F G h).map x).val = ((pasteCylinder hk F' G' h').map x).val := by
  have hac : a = c := (F.map x).property.1.symm.trans
    ((congrArg (Y.source 0) (he x)).trans (F'.map x).property.1)
  have hbd : b = d := (F.map x).property.2.symm.trans
    ((congrArg (Y.target 0) (he x)).trans (F'.map x).property.2)
  subst c d
  have hF : F = F' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (he z)))
  have hG : G = G' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (hf z)))
  subst F' G'
  rfl

lemma pasteCylinder_associative (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{u}}
    (F G H : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : FaceMatching k F G) (i : FaceMatching k G H)
    (h' : FaceMatching k (pasteCylinder hk F G h) H)
    (i' : FaceMatching k F (pasteCylinder hk G H i)) :
    pasteCylinder hk (pasteCylinder hk F G h) H h' =
      pasteCylinder hk F (pasteCylinder hk G H i) i' := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      simp only [pasteCylinder_zero]
      exact horizontalCylinder_associative F G H (zeroFaceMatching_seam h)
        (zeroFaceMatching_seam i) (zeroFaceMatching_seam h') (zeroFaceMatching_seam i')
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let A := (rectangleDiagramOfFunctor F).diagonal
      let B := CylinderComposition.secondDiagonal F G h
      let C := homCast (rectangleDiagramOfFunctor H).diagonal
        ((h.vertices false false).trans (i.vertices false false)).symm
        ((h.vertices true true).trans (i.vertices true true)).symm
      have hab : FaceMatching k A B := CylinderComposition.diagonal_matching F G h
      have hbc : FaceMatching k B C := by
        intro x
        apply Subtype.ext
        change G.map (up ((faceMap n k true).cylinder.nu.map x)) =
          H.map (up ((faceMap n k false).cylinder.nu.map x))
        rw [← tensorFace_up, ← tensorFace_up]
        exact i (up x)
      have hbc_map (x : Table (K.{u} n)) :
          ((pasteCylinder hk' B C hbc).map x).val =
            (pasteCylinder hk G H i).map (up x) := by
        rw [pasteCylinder_succ_up hk']
        exact pasteCylinder_val_congr hk' B C hbc
          (rectangleDiagramOfFunctor G).diagonal (CylinderComposition.secondDiagonal G H i)
          (CylinderComposition.diagonal_matching G H i) (fun _ => rfl) (fun _ => rfl) x
      have habc : FaceMatching k (pasteCylinder hk' A B hab) C := by
        intro x
        apply Subtype.ext
        change ((pasteCylinder hk' A B hab).map ((faceMap n k true).cylinder.nu.map x)).val =
          H.map (up ((faceMap n k false).cylinder.nu.map x))
        erw [← pasteCylinder_succ_up hk' F G h, ← tensorFace_up, ← tensorFace_up]
        exact h' (up x)
      have habc' : FaceMatching k A (pasteCylinder hk' B C hbc) := by
        intro x
        apply Subtype.ext
        change F.map (up ((faceMap n k true).cylinder.nu.map x)) = _
        erw [hbc_map, ← tensorFace_up, ← tensorFace_up]
        exact i' (up x)
      have hassoc := ih n hk' A B C hab hbc habc habc'
      apply functor_ext_rectangle
      · intro a x
        have he : OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu
            (pasteCylinder hk (pasteCylinder hk F G h) H h') =
            OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu
              (pasteCylinder hk F (pasteCylinder hk G H i) i') := by
          apply GlobeComplex.functor_ext
          change (pasteCylinder hk (pasteCylinder hk F G h) H h').map (atEnd a (topTable (n+1))) =
            (pasteCylinder hk F (pasteCylinder hk G H i) i').map (atEnd a (topTable (n+1)))
          simp only [pasteCylinder_endpoint_top]
          exact Y.join_assoc (k+1) _ _ _ (h.ends a) (i.ends a)
        exact congrArg (fun P => P.map x) he
      · intro a
        rw [pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk']
      · intro x
        rw [pasteCylinder_succ_up hk', pasteCylinder_succ_up hk']
        have hl := pasteCylinder_val_congr hk'
          (rectangleDiagramOfFunctor (pasteCylinder hk F G h)).diagonal
          (CylinderComposition.secondDiagonal (pasteCylinder hk F G h) H h')
          (CylinderComposition.diagonal_matching (pasteCylinder hk F G h) H h')
          (pasteCylinder hk' A B hab) C habc
          (fun z => pasteCylinder_succ_up hk' F G h z) (fun _ => rfl) x
        have hr := pasteCylinder_val_congr hk'
          (rectangleDiagramOfFunctor F).diagonal
          (CylinderComposition.secondDiagonal F (pasteCylinder hk G H i) i')
          (CylinderComposition.diagonal_matching F (pasteCylinder hk G H i) i')
          A (pasteCylinder hk' B C hbc) habc' (fun _ => rfl) (fun z => (hbc_map z).symm) x
        exact hl.trans ((congrArg (fun P => (P.map x).val) hassoc).trans hr.symm)
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def restrictCylinder {n : ℕ} (m : ℕ) (b : Bool) {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) : OmegaCategory.Functor (K.{u} m).nu Y :=
  OmegaCategory.Functor.comp (faceMap n m b).cylinder.nu F

@[simp] lemma restrictCylinder_endpoint {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b a : Bool) (x : Table (complex.{u} m)) :
    (restrictCylinder m b F).map (atEnd a x) = F.map (atEnd a ((faceMap n m b).nu.map x)) :=
  congrArg F.map (cylinderHom_atEnd _ a x)

@[simp] lemma restrictCylinder_edge {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b a : Bool) :
    (restrictCylinder (m+1) b F).map (verticalTable (vertex m a)) =
      F.map (verticalTable (vertex n a)) := congrArg F.map (tensorFace_edge n m b a)

@[simp] lemma restrictCylinder_up {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) (x : Table (K.{u} m)) :
    (restrictCylinder (m+1) b F).map (up x) =
      F.map (up ((faceMap n m b).cylinder.nu.map x)) := congrArg F.map (tensorFace_up n m b x)

@[simp] lemma restrictCylinder_self {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b : Bool) : restrictCylinder n b F = F := by
  unfold restrictCylinder
  rw [faceMap_self]
  apply OmegaCategory.Functor.ext
  funext x
  change F.map ((DirectedComplex.Hom.id _).cylinder.nu.map x) = F.map x
  rw [DirectedComplex.Hom.cylinder_id]
  rfl

lemma IntervalMatching.restrict {n : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : IntervalMatching F G) (m : ℕ) (b : Bool) :
    IntervalMatching (restrictCylinder m b F) (restrictCylinder m b G) := by
  intro x
  simp only [restrictCylinder_endpoint]
  exact h _

lemma concatInterval_face (n m : ℕ) (hm : m ≤ n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) (b : Bool) :
    restrictCylinder m b (concatInterval F G h) =
      concatInterval (restrictCylinder m b F) (restrictCylinder m b G) (h.restrict m b) := by
  induction m generalizing n Y with
  | zero =>
    cases n with
    | zero => simp only [restrictCylinder_self]
    | succ n =>
      apply OmegaCategory.Functor.ext
      funext x
      rcases table_zero_cases x with ⟨a,he⟩ | he
      · erw [he, restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · rw [he]
        change (concatInterval F G h).map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))) = _
        rw [verticalTable_natural, faceMap_top]
        change (concatInterval F G h).map (verticalTable (vertex n b)) = _
        rw [concatInterval_succ_edge, concatInterval_zero_vertical]
        change _ = Y.join 0
          (F.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
          (G.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))))
        rw [verticalTable_natural, faceMap_top]
        rfl
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      apply functor_ext_rectangle
      · intro a x
        erw [restrictCylinder_endpoint, concatInterval_endpoint, concatInterval_endpoint]
        cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_endpoint]
      · intro a
        simp only [restrictCylinder_edge, concatInterval_succ_edge]
      · intro x
        erw [restrictCylinder_up, concatInterval_succ_up, concatInterval_succ_up]
        let D := rectangleDiagramOfFunctor F
        let E := rectangleDiagramOfFunctor G
        have he := ih n (by omega) (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h)
          (D.concatDiagonal_matching E h)
        have hl := congrArg (fun P => (P.map x).val) he
        refine hl.trans (concatInterval_val_congr
          (restrictCylinder m b (D.concatDiagonalOne E h))
          (restrictCylinder m b (D.concatDiagonalTwo E h)) _
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalOne
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b))
          ((rectangleDiagramOfFunctor (restrictCylinder (m+1) b F)).concatDiagonalTwo
            (rectangleDiagramOfFunctor (restrictCylinder (m+1) b G)) (h.restrict (m+1) b)) _ ?_ ?_ x)
        · intro z
          change Y.join 0 (F.map (verticalTable (vertex n false)))
            (G.map (up ((faceMap n m b).cylinder.nu.map z))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (verticalTable (vertex m false)))
                ((restrictCylinder (m+1) b G).map (up z))
          erw [restrictCylinder_edge, restrictCylinder_up]
        · intro z
          change Y.join 0 (F.map (up ((faceMap n m b).cylinder.nu.map z)))
            (G.map (verticalTable (vertex n true))) =
              Y.join 0 ((restrictCylinder (m+1) b F).map (up z))
                ((restrictCylinder (m+1) b G).map (verticalTable (vertex m true)))
          erw [restrictCylinder_up, restrictCylinder_edge]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma functor_ext_zero_cylinder {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} 0).nu Y}
    (h : F.map (verticalTable (topTable 0)) = G.map (verticalTable (topTable 0))) : F = G := by
  have he : OmegaCategory.Functor.comp zeroCylinderMap F = OmegaCategory.Functor.comp zeroCylinderMap G := by
    apply GlobeComplex.functor_ext
    change F.map (zeroCylinderMap.map (topTable 1)) = G.map (zeroCylinderMap.map (topTable 1))
    simpa only [zeroCylinderMap_top] using h
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨z,rfl⟩ := zeroCylinderMap_bijective.surjective x
  exact congrArg (fun P => P.map z) he

lemma restrictCylinder_endpoint_top {n m : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) (b a : Bool) :
    (restrictCylinder m b F).map (atEnd a (topTable m)) =
      Y.face m b (F.map (atEnd a (topTable n))) := by
  rw [restrictCylinder_endpoint, faceMap_top, ← atEnd_truncate]
  cases b
  · exact F.map_source m (atEnd a (topTable n))
  · exact F.map_target m (atEnd a (topTable n))

lemma restrictCylinder_zero_vertical {n : ℕ} {Y : OmegaCategory.{v}}
    (F : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (b : Bool) :
    (restrictCylinder 0 b F).map (verticalTable (topTable 0)) =
      F.map (verticalTable (vertex n b)) := by
  change F.map ((faceMap (n+1) 0 b).cylinder.nu.map (verticalTable (topTable 0))) = _
  rw [verticalTable_natural, faceMap_top]
  rfl

lemma pasteCylinder_zero_edge {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching 0 F G) (b : Bool) :
    (pasteCylinder (show 0 < n+1 by omega) F G h).map (verticalTable (vertex n b)) =
      if b then G.map (verticalTable (vertex n true)) else F.map (verticalTable (vertex n false)) :=
  RectangleDiagram.lift_edge _ _

lemma pasteCylinder_zero_up {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching 0 F G) (x : Table (K.{u} n)) :
    (pasteCylinder (show 0 < n+1 by omega) F G h).map (up x) =
      ((concatInterval
        ((rectangleDiagramOfFunctor F).horizontalDiagonalOne (rectangleDiagramOfFunctor G) (zeroFaceMatching_seam h))
        ((rectangleDiagramOfFunctor F).horizontalDiagonalTwo (rectangleDiagramOfFunctor G) (zeroFaceMatching_seam h))
        ((rectangleDiagramOfFunctor F).horizontalDiagonal_matching (rectangleDiagramOfFunctor G) (zeroFaceMatching_seam h))).map x).val :=
  RectangleDiagram.lift_up _ _

lemma pasteCylinder_lower_face (n k i : ℕ) (hk : k < n) (hi : i ≤ k)
    {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) (b : Bool) :
    restrictCylinder i b (pasteCylinder hk F G h) = restrictCylinder i b (if b then G else F) := by
  induction k generalizing n i Y with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    cases n with
    | zero => omega
    | succ n =>
      apply functor_ext_zero_cylinder
      rw [restrictCylinder_zero_vertical, pasteCylinder_zero_edge]
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_zero_vertical]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      cases i with
      | zero =>
        apply functor_ext_zero_cylinder
        rw [restrictCylinder_zero_vertical, pasteCylinder_succ_edge hk']
        cases b
        · exact (restrictCylinder_zero_vertical F false).symm
        · rw [restrictCylinder_zero_vertical]
          exact h.edges true
      | succ i =>
        apply functor_ext_rectangle
        · intro a x
          have he : OmegaCategory.Functor.comp ((complex (i+1)).cylinderEndpoint a).nu
              (restrictCylinder (i+1) b (pasteCylinder hk F G h)) =
              OmegaCategory.Functor.comp ((complex (i+1)).cylinderEndpoint a).nu
                (restrictCylinder (i+1) b (if b then G else F)) := by
            apply GlobeComplex.functor_ext
            change (restrictCylinder (i+1) b (pasteCylinder hk F G h)).map (atEnd a (topTable (i+1))) =
              (restrictCylinder (i+1) b (if b then G else F)).map (atEnd a (topTable (i+1)))
            rw [restrictCylinder_endpoint_top, pasteCylinder_endpoint_top, restrictCylinder_endpoint_top]
            cases b
            · exact Y.join_source_le (i+1) (k+1) _ _ hi (h.ends a)
            · exact Y.join_target_le (i+1) (k+1) _ _ hi (h.ends a)
          exact congrArg (fun P => P.map x) he
        · intro a
          rw [restrictCylinder_edge, pasteCylinder_succ_edge hk']
          cases b
          · exact (restrictCylinder_edge F false a).symm
          · rw [restrictCylinder_edge]
            exact h.edges a
        · intro x
          erw [restrictCylinder_up, pasteCylinder_succ_up hk']
          have he := ih n i hk' (by omega) (rectangleDiagramOfFunctor F).diagonal
            (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
          have hev := congrArg (fun P => (P.map x).val) he
          refine hev.trans ?_
          cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, restrictCylinder_up]
          all_goals rfl

end Thomason.GrayRecursive

end

end OAI
