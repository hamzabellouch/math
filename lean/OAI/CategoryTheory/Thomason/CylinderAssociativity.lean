import Mathlib
import OAI.CategoryTheory.Thomason.CylinderFaces

namespace OAI

/-! Cylinder Associativity. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma hom_join_val {Y : OmegaCategory.{v}} {a b : Y.Cell} (k : ℕ)
    (x y : (Y.homCategory a b).Cell)
    (h : (Y.homCategory a b).target k x = (Y.homCategory a b).source k y) :
    ((Y.homCategory a b).join k x y).val = Y.join (k+1) x.val y.val := by
  rw [(Y.homCategory a b).join_eq k x y h, Y.join_eq (k+1) _ _ (congrArg Subtype.val h)]
  rfl

structure CylinderComposition (n k : ℕ) where
  compose : {Y : OmegaCategory.{v}} →
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) → FaceMatching k F G →
      OmegaCategory.Functor (K.{u} n).nu Y
  endpoint_top : ∀ {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) (a : Bool),
    (compose F G h).map (atEnd a (topTable n)) =
      Y.join k (F.map (atEnd a (topTable n))) (G.map (atEnd a (topTable n)))

lemma CylinderComposition.endpoint {n k : ℕ} (C : CylinderComposition.{u,v} n k)
    (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (a : Bool) (x : Table (complex.{u} n)) :
    (C.compose F G h).map (atEnd a x) =
      (globeComposite hk
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F)
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu G) (h.ends a)).map x := by
  have he : OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu (C.compose F G h) =
      globeComposite hk
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F)
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu G) (h.ends a) := by
    apply GlobeComplex.functor_ext
    erw [globeComposite_top]
    exact C.endpoint_top F G h a
  exact congrArg (fun A => A.map x) he

lemma zeroFaceMatching_seam {n : ℕ} {Y : OmegaCategory.{v}}
    {F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y} (h : FaceMatching 0 F G) :
    F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)) := by
  have h' := h (verticalTable (topTable 0))
  simpa only [verticalTable_natural, faceMap_top, vertex] using h'

def cylinderCompositionZero (n : ℕ) : CylinderComposition.{u,v} (n+1) 0 where
  compose F G h := horizontalCylinder F G (zeroFaceMatching_seam h)
  endpoint_top F G h a := by
    rw [horizontalCylinder_endpoint]
    exact lift_top _ _

namespace CylinderComposition
variable {n k : ℕ} (C : CylinderComposition.{u,v} n k) (hk : k < n)
    {Y : OmegaCategory.{v}} (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : FaceMatching (k+1) F G)

def secondDiagonal : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory (F.map (atEnd false (vertex n false))) (F.map (atEnd true (vertex n true)))) :=
  homCast (rectangleDiagramOfFunctor G).diagonal (h.vertices false false).symm (h.vertices true true).symm

lemma diagonal_matching : FaceMatching k (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h) := by
  intro x
  apply Subtype.ext
  change F.map (up ((faceMap n k true).cylinder.nu.map x)) =
    G.map (up ((faceMap n k false).cylinder.nu.map x))
  rw [← tensorFace_up, ← tensorFace_up]
  exact h (up x)

def positiveEnds (a : Bool) : OmegaCategory.Functor (complex.{u} (n+1)).nu Y :=
  globeComposite (Nat.add_lt_add_right hk 1) ((rectangleDiagramOfFunctor F).ends a)
    ((rectangleDiagramOfFunctor G).ends a) (h.ends a)

lemma positiveEnds_vertex (a b : Bool) :
    (positiveEnds hk F G h a).map (vertex n b) = F.map (atEnd a (vertex n b)) :=
  globeComposite_vertex hk _ _ _ b

def positiveDiagram : RectangleDiagram.{u,v} n Y :=
  rectangleDiagramOfTop (positiveEnds hk F G h)
    (rectangleDiagramOfFunctor F).edge (rectangleDiagramOfFunctor F).edge_fixed
    (fun a => ((rectangleDiagramOfFunctor F).edge_source a).trans (positiveEnds_vertex hk F G h false a).symm)
    (fun a => ((rectangleDiagramOfFunctor F).edge_target a).trans (positiveEnds_vertex hk F G h true a).symm)
    (homCast (C.compose (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h)
      (diagonal_matching F G h))
      (positiveEnds_vertex hk F G h false false).symm (positiveEnds_vertex hk F G h true true).symm)
    (by
      change ((C.compose (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h)
        (diagonal_matching F G h)).map (atEnd false (topTable n))).val = _
      erw [C.endpoint_top, hom_join_val _ _ _ ((diagonal_matching F G h).ends false)]
      change Y.join (k+1) ((rectangleDiagramOfFunctor F).diagonal.map (atEnd false (topTable n))).val
        ((rectangleDiagramOfFunctor G).diagonal.map (atEnd false (topTable n))).val = _
      rw [(rectangleDiagramOfFunctor F).left, (rectangleDiagramOfFunctor G).left, suspendTable_top]
      change Y.join (k+1) (Y.join 0 _ _) (Y.join 0 _ _) =
        Y.join 0 ((rectangleDiagramOfFunctor F).edge false)
          ((globeComposite _ _ _ _).map (topTable (n+1)))
      erw [globeComposite_top]
      have hedge : (rectangleDiagramOfFunctor G).edge false = (rectangleDiagramOfFunctor F).edge false :=
        (h.edges false).symm
      rw [hedge]
      exact (Y.join_whisker_left 0 (k+1) (by omega) _ _ _
        (Y.source_fixed_upwards (show 1 ≤ k+1 by omega) ((rectangleDiagramOfFunctor F).edge_fixed false))
        (h.ends true) (by
          have hh := (rectangleDiagramOfFunctor F).edge_end_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)
        (by
          rw [← hedge]
          have hh := (rectangleDiagramOfFunctor G).edge_end_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)).symm)
    (by
      change ((C.compose (rectangleDiagramOfFunctor F).diagonal (secondDiagonal F G h)
        (diagonal_matching F G h)).map (atEnd true (topTable n))).val = _
      erw [C.endpoint_top, hom_join_val _ _ _ ((diagonal_matching F G h).ends true)]
      change Y.join (k+1) ((rectangleDiagramOfFunctor F).diagonal.map (atEnd true (topTable n))).val
        ((rectangleDiagramOfFunctor G).diagonal.map (atEnd true (topTable n))).val = _
      rw [(rectangleDiagramOfFunctor F).right, (rectangleDiagramOfFunctor G).right, suspendTable_top]
      change Y.join (k+1) (Y.join 0 _ _) (Y.join 0 _ _) =
        Y.join 0 ((globeComposite _ _ _ _).map (topTable (n+1)))
          ((rectangleDiagramOfFunctor F).edge true)
      erw [globeComposite_top]
      have hedge : (rectangleDiagramOfFunctor G).edge true = (rectangleDiagramOfFunctor F).edge true :=
        (h.edges true).symm
      rw [hedge]
      exact (Y.join_whisker_right 0 (k+1) (by omega) _ _ _
        (Y.source_fixed_upwards (show 1 ≤ k+1 by omega) ((rectangleDiagramOfFunctor F).edge_fixed true))
        (h.ends false) (by
          have hh := (rectangleDiagramOfFunctor F).end_edge_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)
        (by
          rw [← hedge]
          have hh := (rectangleDiagramOfFunctor G).end_edge_matching (topTable n)
          rw [suspendTable_top] at hh
          exact hh)).symm)

def succ : CylinderComposition.{u,v} (n+1) (k+1) where
  compose F G h := (C.positiveDiagram hk F G h).lift
  endpoint_top F G h a := by
    erw [RectangleDiagram.lift_endpoint]
    change (globeComposite (Nat.add_lt_add_right hk 1) _ _ (h.ends a)).map (topTable (n+1)) = _
    erw [globeComposite_top]
    rfl

end CylinderComposition

def cylinderComposition (n k : ℕ) (hk : k < n) : CylinderComposition.{u,v} n k :=
  match n, k with
  | 0, _ => False.elim (by omega)
  | n+1, 0 => cylinderCompositionZero n
  | n+1, k+1 => (cylinderComposition n k (by omega)).succ (by omega)

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

abbrev pasteCylinder {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) :=
  (cylinderComposition n k hk).compose F G h

lemma pasteCylinder_endpoint_top {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) (a : Bool) :
    (pasteCylinder hk F G h).map (atEnd a (topTable n)) =
      Y.join k (F.map (atEnd a (topTable n))) (G.map (atEnd a (topTable n))) :=
  (cylinderComposition n k hk).endpoint_top F G h a

lemma pasteCylinder_endpoint {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (a : Bool) (x : Table (complex.{u} n)) :
    (pasteCylinder hk F G h).map (atEnd a x) =
      (globeComposite hk
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu F)
        (OmegaCategory.Functor.comp ((complex n).cylinderEndpoint a).nu G) (h.ends a)).map x :=
  (cylinderComposition n k hk).endpoint hk F G h a x

lemma pasteCylinder_zero {n : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching 0 F G) :
    pasteCylinder (show 0 < n+1 by omega) F G h =
      horizontalCylinder F G (zeroFaceMatching_seam h) := rfl

lemma pasteCylinder_succ_edge {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching (k+1) F G) (a : Bool) :
    (pasteCylinder (Nat.add_lt_add_right hk 1) F G h).map (verticalTable (vertex n a)) =
      F.map (verticalTable (vertex n a)) := RectangleDiagram.lift_edge _ _

lemma pasteCylinder_succ_up {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching (k+1) F G)
    (x : Table (K.{u} n)) :
    (pasteCylinder (Nat.add_lt_add_right hk 1) F G h).map (up x) =
      ((pasteCylinder hk (rectangleDiagramOfFunctor F).diagonal (CylinderComposition.secondDiagonal F G h)
        (CylinderComposition.diagonal_matching F G h)).map x).val := RectangleDiagram.lift_up _ _

lemma pasteCylinder_natural (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}} {Z : OmegaCategory.{w}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G)
    (P : OmegaCategory.Functor Y Z) :
    OmegaCategory.Functor.comp (pasteCylinder hk F G h) P =
      pasteCylinder hk (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P) (h.natural P) := by
  induction k generalizing n Y Z with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      rw [pasteCylinder_zero, pasteCylinder_zero]
      exact horizontalCylinder_natural F G _ P
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      apply functor_ext_rectangle
      · intro a x
        change P.map ((pasteCylinder hk F G h).map (atEnd a x)) = _
        rw [pasteCylinder_endpoint, pasteCylinder_endpoint]
        exact congrArg (fun U => U.map x) (globeComposite_natural hk
          (OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu F)
          (OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu G) (h.ends a) P)
      · intro a
        change P.map ((pasteCylinder hk F G h).map (verticalTable (vertex n a))) = _
        rw [pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk']
        rfl
      · intro x
        change P.map ((pasteCylinder hk F G h).map (up x)) = _
        rw [pasteCylinder_succ_up hk', pasteCylinder_succ_up hk']
        have he := ih n hk' (rectangleDiagramOfFunctor F).diagonal
          (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
          (P.homMap (F.map (atEnd false (vertex n false))) (F.map (atEnd true (vertex n true))))
        exact congrArg (fun U => (U.map x).val) he

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma globeSuspended_ext {n : ℕ} {Y : OmegaCategory.{v}} {a b : Y.Cell}
    (A : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (B : OmegaCategory.Functor (complex.{u} (n+1)).nu Y)
    (h : (A.map (topTable n)).val = B.map (topTable (n+1))) (x : Table (complex.{u} n)) :
    (A.map x).val = B.map (suspendTable x) := by
  obtain ⟨p,c,hp,he⟩ := table_classification x
  rw [he, suspendTable_eq_face]
  erw [← face_nu n p c (topTable n), A.map_face,
    ← face_nu (n+1) (p+1) c (topTable (n+1)), B.map_face]
  cases c
  · change Y.source (p+1) (A.map (topTable n)).val = Y.source (p+1) (B.map (topTable (n+1)))
    rw [h]
  · change Y.target (p+1) (A.map (topTable n)).val = Y.target (p+1) (B.map (topTable (n+1)))
    rw [h]

lemma constantInterval_faceMatching {n k : ℕ} {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    FaceMatching k (constantInterval F) (constantInterval G) := by
  have he : OmegaCategory.Functor.comp (faceMap n k true).nu F =
      OmegaCategory.Functor.comp (faceMap n k false).nu G := by
    apply GlobeComplex.functor_ext
    change F.map ((faceMap n k true).nu.map (topTable k)) =
      G.map ((faceMap n k false).nu.map (topTable k))
    rw [faceMap_top, faceMap_top]
    exact (F.map_target k (topTable n)).trans (h.trans (G.map_source k (topTable n)).symm)
  intro x
  have h₀ := congrArg (fun U => U.nu.map x) (faceMap.{u} n k true).cylinder_projection
  have h₁ := congrArg (fun U => U.nu.map x) (faceMap.{u} n k false).cylinder_projection
  change project ((faceMap n k true).cylinder.nu.map x) = (faceMap n k true).nu.map (project x) at h₀
  change project ((faceMap n k false).cylinder.nu.map x) = (faceMap n k false).nu.map (project x) at h₁
  erw [constantInterval_map F, constantInterval_map G, h₀, h₁]
  exact congrArg (fun U => U.map (project x)) he

lemma pasteCylinder_constant (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{v}}
    (F G : OmegaCategory.Functor (complex.{u} n).nu Y)
    (h : Y.target k (F.map (topTable n)) = Y.source k (G.map (topTable n))) :
    pasteCylinder hk (constantInterval F) (constantInterval G) (constantInterval_faceMatching F G h) =
      constantInterval (globeComposite hk F G h) := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      have h' : F.map (vertex n true) = G.map (vertex n false) := by
        erw [← F.map_target, ← G.map_source] at h
        exact h
      rw [pasteCylinder_zero, horizontalCylinder_constant F G h']
      rfl
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      let hc := constantInterval_faceMatching F G h
      apply functor_ext_rectangle
      · intro a x
        rw [pasteCylinder_endpoint, constantInterval_endpoint]
        have hF : OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu (constantInterval F) = F :=
          constantInterval_ends F a
        have hG : OmegaCategory.Functor.comp ((complex (n+1)).cylinderEndpoint a).nu (constantInterval G) = G :=
          constantInterval_ends G a
        simp only [hF, hG]
      · intro a
        rw [pasteCylinder_succ_edge hk', constantInterval_edge, constantInterval_edge]
        exact (globeComposite_vertex hk' F G h a).symm
      · intro x
        rw [pasteCylinder_succ_up hk', constantInterval_up]
        let A := homCast (globeHomMap F)
          (constantInterval_endpoint F false (vertex n false)).symm
          (constantInterval_endpoint F true (vertex n true)).symm
        let B := homCast (globeHomMap G)
          ((globeMatching_vertex F G h false).symm.trans (constantInterval_endpoint F false (vertex n false)).symm)
          ((globeMatching_vertex F G h true).symm.trans (constantInterval_endpoint F true (vertex n true)).symm)
        have hA : (rectangleDiagramOfFunctor (constantInterval F)).diagonal = constantInterval A := by
          apply OmegaCategory.Functor.ext
          funext y
          apply Subtype.ext
          exact constantInterval_up F y
        have hB : CylinderComposition.secondDiagonal (constantInterval F) (constantInterval G) hc =
            constantInterval B := by
          apply OmegaCategory.Functor.ext
          funext y
          apply Subtype.ext
          exact constantInterval_up G y
        have hAB : (Y.homCategory ((constantInterval F).map (atEnd false (vertex n false)))
            ((constantInterval F).map (atEnd true (vertex n true)))).target k (A.map (topTable n)) =
            (Y.homCategory ((constantInterval F).map (atEnd false (vertex n false)))
            ((constantInterval F).map (atEnd true (vertex n true)))).source k (B.map (topTable n)) := by
          apply Subtype.ext
          change Y.target (k+1) (F.map (suspendTable (topTable n))) =
            Y.source (k+1) (G.map (suspendTable (topTable n)))
          rw [suspendTable_top]
          exact h
        simp only [hA, hB]
        erw [ih n hk' A B hAB]
        rw [constantInterval_map]
        apply globeSuspended_ext _ (globeComposite hk F G h)
        rw [globeComposite_top, hom_join_val _ _ _ hAB, globeComposite_top]
        change Y.join (k+1) (F.map (suspendTable (topTable n))) (G.map (suspendTable (topTable n))) = _
        rw [suspendTable_top]

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory Limits DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory GrayComposition

lemma pushout_faceMatching (n k : ℕ) : FaceMatching k (j₀.{u} n k) (j₁.{u} n k) := by
  intro x
  exact congrArg (fun f : T.{u} k ⟶ Q.{u} n k => f.map x)
    (pushout.condition (f := tensorFace.{u} n k true) (g := tensorFace.{u} n k false))

def cooperation (n k : ℕ) (hk : k < n) : T.{u} n ⟶ Q.{u} n k :=
  pasteCylinder hk (j₀.{u} n k) (j₁.{u} n k) (pushout_faceMatching n k)

lemma cooperation_endpoint (n k : ℕ) (hk : k < n) (b : Bool) :
    endpoint.{u} n b ≫ cooperation n k hk =
      composition.{u} n k hk ≫ cutEndpoint.{u} n k b := by
  apply GlobeComplex.functor_ext
  change (cooperation n k hk).map (atEnd b (topTable n)) =
    (cutEndpoint.{u} n k b).map ((composition.{u} n k hk).map (topTable n))
  rw [cooperation, pasteCylinder_endpoint_top, composition, lift_top]
  unfold compositeCell
  rw [(cutEndpoint.{u} n k b).map_comp _ _ _ _
    ((cutEndpoint.{u} n k b).map_composable (top_composable.{u} n k))]
  have h₀ : (cutEndpoint.{u} n k b).map ((i₀.{u} n k).map (topTable n)) =
      (j₀.{u} n k).map (atEnd b (topTable n)) := by
    change ((i₀ n k) ≫ cutEndpoint n k b).map _ = _
    simp only [cutEndpoint, i₀, pushout.inl_desc]
    rfl
  have h₁ : (cutEndpoint.{u} n k b).map ((i₁.{u} n k).map (topTable n)) =
      (j₁.{u} n k).map (atEnd b (topTable n)) := by
    change ((i₁ n k) ≫ cutEndpoint n k b).map _ = _
    simp only [cutEndpoint, i₁, pushout.inr_desc]
    rfl
  simp only [h₀, h₁]
  exact (Q.{u} n k).join_eq k _ _ _

lemma pushout_globe_composition (n k : ℕ) (hk : k < n) :
    globeComposite hk (i₀.{u} n k) (i₁.{u} n k) (top_composable.{u} n k) = composition.{u} n k hk := by
  apply GlobeComplex.functor_ext
  rw [globeComposite_top, composition, lift_top]
  exact (P.{u} n k).join_eq k _ _ _

lemma cooperation_projection (n k : ℕ) (hk : k < n) :
    cooperation.{u} n k hk ≫ cutProjection.{u} n k =
      projection.{u} n ≫ composition.{u} n k hk := by
  have h₀ : OmegaCategory.Functor.comp (j₀.{u} n k) (cutProjection.{u} n k) =
      constantInterval (i₀.{u} n k) := by
    change j₀ n k ≫ cutProjection n k = _
    simp only [cutProjection, j₀, pushout.inl_desc]
    rfl
  have h₁ : OmegaCategory.Functor.comp (j₁.{u} n k) (cutProjection.{u} n k) =
      constantInterval (i₁.{u} n k) := by
    change j₁ n k ≫ cutProjection n k = _
    simp only [cutProjection, j₁, pushout.inr_desc]
    rfl
  change OmegaCategory.Functor.comp (pasteCylinder _ _ _ _) _ = _
  rw [pasteCylinder_natural]
  simp only [h₀, h₁]
  rw [pasteCylinder_constant _ _ hk _ _ (top_composable.{u} n k), pushout_globe_composition]
  rfl

theorem cooperationExists_all (n k : ℕ) (hk : k < n) : CooperationExists.{u} n k hk :=
  ⟨cooperation n k hk, cooperation_endpoint n k hk, cooperation_projection n k hk⟩
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory Limits DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
@[ext] lemma ext {n : ℕ} {Y : OmegaCategory.{v}} {D E : RectangleDiagram.{u,v} n Y}
    (he : D.ends = E.ends) (hv : D.edge = E.edge)
    (hd : ∀ x, (D.diagonal.map x).val = (E.diagonal.map x).val) : D = E := by
  cases D
  cases E
  cases he
  cases hv
  congr 1
  apply OmegaCategory.Functor.ext
  funext x
  exact Subtype.ext (hd x)

@[simp] lemma ofFunctor_lift {n : ℕ} {Y : OmegaCategory.{v}} (D : RectangleDiagram.{u,v} n Y) :
    rectangleDiagramOfFunctor D.lift = D := by
  apply ext
  · funext a
    apply OmegaCategory.Functor.ext
    funext x
    exact D.lift_endpoint a x
  · funext a
    exact D.lift_edge a
  · intro x
    exact D.lift_up x
end RectangleDiagram

namespace IntervalMatching
variable {n : ℕ} {Y : OmegaCategory.{v}} {F G H : OmegaCategory.Functor (K.{u} n).nu Y}
lemma concat_left (h : IntervalMatching F G) (i : IntervalMatching G H) :
    IntervalMatching (concatInterval F G h) H := by
  intro x
  rw [concatInterval_endpoint]
  exact i x
lemma concat_right (h : IntervalMatching F G) (i : IntervalMatching G H) :
    IntervalMatching F (concatInterval G H i) := by
  intro x
  rw [concatInterval_endpoint]
  exact h x
lemma natural (h : IntervalMatching F G) {Z : OmegaCategory.{w}}
    (P : OmegaCategory.Functor Y Z) :
    IntervalMatching (OmegaCategory.Functor.comp F P) (OmegaCategory.Functor.comp G P) :=
  fun x => congrArg P.map (h x)
end IntervalMatching

abbrev pairFunctor {X Y Z : OmegaCategory.{u}} (F : X ⟶ Y) (G : X ⟶ Z) :
    X ⟶ Y ⨯ Z := prod.lift F G

lemma concatInterval_pair {n : ℕ} {Y Z : OmegaCategory.{u}}
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu Z) (h' : IntervalMatching F' G')
    (H : IntervalMatching (pairFunctor F F') (pairFunctor G G')) :
    concatInterval (pairFunctor F F') (pairFunctor G G') H =
      pairFunctor (concatInterval F G h) (concatInterval F' G' h') := by
  apply @prod.hom_ext OmegaCategory.{u} _ ((K n).nu) Y Z _
  · change OmegaCategory.Functor.comp (concatInterval _ _ H) (prod.fst : Y ⨯ Z ⟶ Y) = _
    rw [concatInterval_natural]
    change concatInterval ((pairFunctor F F') ≫ prod.fst) ((pairFunctor G G') ≫ prod.fst) _ = _
    simp only [pairFunctor, prod.lift_fst]
  · change OmegaCategory.Functor.comp (concatInterval _ _ H) (prod.snd : Y ⨯ Z ⟶ Z) = _
    rw [concatInterval_natural]
    change concatInterval ((pairFunctor F F') ≫ prod.snd) ((pairFunctor G G') ≫ prod.snd) _ = _
    simp only [pairFunctor, prod.lift_snd]

lemma IntervalMatching.pair {n : ℕ} {Y Z : OmegaCategory.{u}}
    {F G : OmegaCategory.Functor (K.{u} n).nu Y} (h : IntervalMatching F G)
    {F' G' : OmegaCategory.Functor (K.{u} n).nu Z} (h' : IntervalMatching F' G') :
    IntervalMatching (pairFunctor F F') (pairFunctor G G') := by
  have he : ((complex n).cylinderEndpoint true).nu ≫ pairFunctor F F' =
      ((complex n).cylinderEndpoint false).nu ≫ pairFunctor G G' := by
    apply prod.hom_ext <;> simp only [Category.assoc, pairFunctor, prod.lift_fst, prod.lift_snd]
    · exact OmegaCategory.Functor.ext (funext h)
    · exact OmegaCategory.Functor.ext (funext h')
  exact fun x => congrArg (fun f => f.map x) he

lemma concatInterval_homCompose {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h' : IntervalMatching F' G') :
    concatInterval (homCompose F F') (homCompose G G')
      (fun x => by apply Subtype.ext
                   change Y.join 0 (F.map (atEnd true x)).val (F'.map (atEnd true x)).val = _
                   rw [h x, h' x]; rfl) =
      homCompose (concatInterval F G h) (concatInterval F' G' h') := by
  let P : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ Y.homCategory a c :=
    homCompose (prod.fst : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _) (prod.snd : (Y.homCategory a b ⨯ Y.homCategory b c) ⟶ _)
  have hp (A : (K.{u} n).nu ⟶ Y.homCategory a b)
      (B : (K.{u} n).nu ⟶ Y.homCategory b c) :
      pairFunctor A B ≫ P = homCompose A B := by
    apply OmegaCategory.Functor.ext
    funext x
    apply Subtype.ext
    change Y.join 0 ((pairFunctor A B ≫ prod.fst).map x).val
      ((pairFunctor A B ≫ prod.snd).map x).val = _
    change Y.join 0 ((prod.lift A B ≫ prod.fst).map x).val ((prod.lift A B ≫ prod.snd).map x).val = _
    rw [prod.lift_fst, prod.lift_snd]
    rfl
  have he := concatInterval_natural n (pairFunctor F F') (pairFunctor G G') (h.pair h') P
  change concatInterval _ _ _ ≫ P = concatInterval (pairFunctor F F' ≫ P) (pairFunctor G G' ≫ P) _ at he
  simp only [concatInterval_pair F G h F' G' h', hp] at he
  exact he.symm

lemma IntervalMatching.constantAt {n : ℕ} {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) :
    IntervalMatching (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) :=
  fun _ => rfl

@[simp] lemma concatInterval_constantAt {n : ℕ} {Y : OmegaCategory.{v}} (a : Y.Cell)
    (ha : Y.source 0 a = a) (h : IntervalMatching (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha)) :
    concatInterval (constantAt (K.{u} n).nu a ha) (constantAt (K.{u} n).nu a ha) h =
      constantAt (K.{u} n).nu a ha :=
  concatInterval_constant n (constantAt (complex n).nu a ha)

lemma concatInterval_val_congr {n : ℕ} {Y : OmegaCategory.{v}} {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d)) (h' : IntervalMatching F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) (x : Table (K.{u} n)) :
    ((concatInterval F G h).map x).val = ((concatInterval F' G' h').map x).val := by
  have hac : a = c := (F.map x).property.1.symm.trans
    ((congrArg (Y.source 0) (he x)).trans (F'.map x).property.1)
  have hbd : b = d := (F.map x).property.2.symm.trans
    ((congrArg (Y.target 0) (he x)).trans (F'.map x).property.2)
  subst c d
  have hF : F = F' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (he z)))
  have hG : G = G' := OmegaCategory.Functor.ext (funext (fun z => Subtype.ext (hf z)))
  subst F' G'
  rfl

lemma concatInterval_homCompose_left {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = a) (ht : Y.target 0 f = b)
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : IntervalMatching F G)
    (h' : IntervalMatching (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G)) :
    concatInterval (homCompose (constantHom (K n).nu f hf hs ht) F)
      (homCompose (constantHom (K n).nu f hf hs ht) G) h' =
      homCompose (constantHom (K n).nu f hf hs ht) (concatInterval F G h) := by
  have e := concatInterval_homCompose (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (IntervalMatching.constantAt (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf)) F G h
  exact e.trans (congrArg (fun A => homCompose A (concatInterval F G h))
    (concatInterval_constantAt (Y := Y.homCategory a b) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

lemma concatInterval_homCompose_right {n : ℕ} {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : IntervalMatching F G)
    (f : Y.Cell) (hf : Y.source 1 f = f) (hs : Y.source 0 f = b) (ht : Y.target 0 f = c)
    (h' : IntervalMatching (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht))) :
    concatInterval (homCompose F (constantHom (K n).nu f hf hs ht))
      (homCompose G (constantHom (K n).nu f hf hs ht)) h' =
      homCompose (concatInterval F G h) (constantHom (K n).nu f hf hs ht) := by
  have e := concatInterval_homCompose F G h (constantHom (K n).nu f hf hs ht)
    (constantHom (K n).nu f hf hs ht) (IntervalMatching.constantAt (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf))
  exact e.trans (congrArg (fun B => homCompose (concatInterval F G h) B)
    (concatInterval_constantAt (Y := Y.homCategory b c) ⟨f, hs, ht⟩ (Subtype.ext hf) _))

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def IntervalAssociative (n : ℕ) : Prop :=
  ∀ {Y : OmegaCategory.{u}} (F G H : OmegaCategory.Functor (K.{u} n).nu Y)
    (h : IntervalMatching F G) (i : IntervalMatching G H),
    concatInterval (concatInterval F G h) H (h.concat_left i) =
      concatInterval F (concatInterval G H i) (h.concat_right i)

namespace RectangleDiagram
variable {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S : RectangleDiagram.{u,u} n Y)
    (h : ∀ x, (D.ends true).map x = (E.ends false).map x)
    (i : ∀ x, (E.ends true).map x = (S.ends false).map x)

def assocLeft : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends false).map (vertex n false)) ((E.ends false).map (vertex n false))) :=
  constantHom _ (D.edge false) (D.edge_fixed false) (D.edge_source false)
    ((D.edge_target false).trans (h _))

def assocRight : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((E.ends true).map (vertex n true)) ((S.ends true).map (vertex n true))) :=
  constantHom _ (S.edge true) (S.edge_fixed true)
    ((S.edge_source true).trans (i _).symm) (S.edge_target true)

def assocA := homCompose (D.assocLeft E h) (E.concatDiagonalOne S i)
def assocB := homCompose (D.assocLeft E h) (E.concatDiagonalTwo S i)
def assocC := homCompose (D.concatDiagonalTwo E h) (E.assocRight S i)

lemma assocB_map (x : Table (K.{u} n)) :
    ((D.assocB E S h i).map x).val =
      ((homCompose (D.concatDiagonalOne E h) (E.assocRight S i)).map x).val := by
  change Y.join 0 (D.edge false) (Y.join 0 (E.diagonal.map x).val (S.edge true)) =
    Y.join 0 (Y.join 0 (D.edge false) (E.diagonal.map x).val) (S.edge true)
  exact (Y.join_assoc 0 _ _ _
    ((D.edge_target false).trans ((h _).trans (E.diagonal.map x).property.1.symm))
    ((E.diagonal.map x).property.2.trans ((i _).trans (S.edge_source true).symm))).symm

lemma assocAB : IntervalMatching (D.assocA E S h i) (D.assocB E S h i) := by
  intro x
  apply Subtype.ext
  change Y.join 0 (D.edge false) ((E.concatDiagonalOne S i).map (atEnd true x)).val =
    Y.join 0 (D.edge false) ((E.concatDiagonalTwo S i).map (atEnd false x)).val
  rw [E.concatDiagonal_matching S i x]

lemma assocBC : IntervalMatching (D.assocB E S h i) (D.assocC E S h i) := by
  intro x
  apply Subtype.ext
  rw [D.assocB_map E S h i]
  change Y.join 0 ((D.concatDiagonalOne E h).map (atEnd true x)).val (S.edge true) =
    Y.join 0 ((D.concatDiagonalTwo E h).map (atEnd false x)).val (S.edge true)
  rw [D.concatDiagonal_matching E h x]

lemma concat_one_assoc :
    (D.concat E h (intervalComposition n)).concatDiagonalOne S i = D.assocA E S h i := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (Y.join 0 (D.edge false) (E.edge false)) (S.diagonal.map x).val =
    Y.join 0 (D.edge false) (Y.join 0 (E.edge false) (S.diagonal.map x).val)
  exact Y.join_assoc 0 _ _ _ (D.seam_edge E h false)
    ((E.edge_target false).trans ((i _).trans (S.diagonal.map x).property.1.symm))

lemma concat_two_assoc :
    (D.concat E h (intervalComposition n)).concatDiagonalTwo S i =
      concatInterval (D.assocB E S h i) (D.assocC E S h i) (D.assocBC E S h i) := by
  have hb : D.assocB E S h i = homCompose (D.concatDiagonalOne E h) (E.assocRight S i) :=
    OmegaCategory.Functor.ext (funext (fun x => Subtype.ext (D.assocB_map E S h i x)))
  have hm : IntervalMatching (homCompose (D.concatDiagonalOne E h) (E.assocRight S i))
      (homCompose (D.concatDiagonalTwo E h) (E.assocRight S i)) := by
    simpa only [assocC, ← hb] using D.assocBC E S h i
  have he := concatInterval_homCompose_right
    (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h)
    (S.edge true) (S.edge_fixed true) ((S.edge_source true).trans (i _).symm) (S.edge_target true) hm
  simp only [show constantHom (K n).nu (S.edge true) (S.edge_fixed true)
    ((S.edge_source true).trans (i _).symm) (S.edge_target true) = E.assocRight S i from rfl, ← hb] at he
  exact he.symm

lemma concat_one_assoc' :
    D.concatDiagonalOne (E.concat S i (intervalComposition n)) h =
      concatInterval (D.assocA E S h i) (D.assocB E S h i) (D.assocAB E S h i) := by
  exact (concatInterval_homCompose_left
    (D.edge false) (D.edge_fixed false) (D.edge_source false) ((D.edge_target false).trans (h _))
    (E.concatDiagonalOne S i) (E.concatDiagonalTwo S i) (E.concatDiagonal_matching S i)
    (D.assocAB E S h i)).symm

lemma concat_two_assoc' :
    D.concatDiagonalTwo (E.concat S i (intervalComposition n)) h = D.assocC E S h i := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map x).val (Y.join 0 (E.edge true) (S.edge true)) =
    Y.join 0 (Y.join 0 (D.diagonal.map x).val (E.edge true)) (S.edge true)
  exact (Y.join_assoc 0 _ _ _
    ((D.diagonal.map x).property.2.trans ((h _).trans (E.edge_source true).symm))
    (E.seam_edge S i true)).symm

lemma concat_assoc (ih : IntervalAssociative.{u} n) :
    (D.concat E h (intervalComposition n)).concat S i (intervalComposition n) =
      D.concat (E.concat S i (intervalComposition n)) h (intervalComposition n) := by
  apply RectangleDiagram.ext
  · funext a
    cases a <;> rfl
  · funext a
    exact Y.join_assoc 0 _ _ _ (D.seam_edge E h a) (E.seam_edge S i a)
  · intro x
    change ((concatInterval ((D.concat E h (intervalComposition n)).concatDiagonalOne S i)
      ((D.concat E h (intervalComposition n)).concatDiagonalTwo S i) _).map x).val =
      ((concatInterval (D.concatDiagonalOne (E.concat S i (intervalComposition n)) h)
        (D.concatDiagonalTwo (E.concat S i (intervalComposition n)) h) _).map x).val
    simp only [concat_one_assoc, concat_two_assoc, concat_one_assoc', concat_two_assoc']
    exact congrArg (fun F => (F.map x).val)
      (ih (D.assocA E S h i) (D.assocB E S h i) (D.assocC E S h i)
        (D.assocAB E S h i) (D.assocBC E S h i)).symm

end RectangleDiagram

lemma concatInterval_associative (n : ℕ) : IntervalAssociative.{u} n := by
  induction n with
  | zero =>
    intro Y F G H h i
    apply OmegaCategory.Functor.ext
    funext x
    rcases table_zero_cases x with ⟨a,he⟩ | he
    · rw [he]
      simp only [concatInterval_endpoint]
      cases a <;> rfl
    · rw [he]
      simp only [concatInterval_zero_vertical]
      exact Y.join_assoc 0 _ _ _ (zero_interval_seam F G h) (zero_interval_seam G H i)
  | succ n ih =>
    intro Y F G H h i
    have he := (rectangleDiagramOfFunctor F).concat_assoc (rectangleDiagramOfFunctor G)
      (rectangleDiagramOfFunctor H) h i ih
    change (((rectangleDiagramOfFunctor (concatInterval F G h)).concat
      (rectangleDiagramOfFunctor H) _ (intervalComposition n)).lift) =
      (((rectangleDiagramOfFunctor F).concat (rectangleDiagramOfFunctor (concatInterval G H i))
        _ (intervalComposition n)).lift)
    simp only [show concatInterval F G h = ((rectangleDiagramOfFunctor F).concat
      (rectangleDiagramOfFunctor G) h (intervalComposition n)).lift from rfl,
      show concatInterval G H i = ((rectangleDiagramOfFunctor G).concat
        (rectangleDiagramOfFunctor H) i (intervalComposition n)).lift from rfl,
      RectangleDiagram.ofFunctor_lift]
    exact congrArg RectangleDiagram.lift he
end Thomason.GrayRecursive

end

end OAI
