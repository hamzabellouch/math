import Mathlib
import OAI.CategoryTheory.Thomason.CylinderInterchange

namespace OAI

/-! Pasting Interchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace RectangleDiagram
namespace MixedZero
variable {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S T : RectangleDiagram.{u,u} n Y)
    (e : D.edge true = E.edge false) (j : S.edge true = T.edge false)
    (h : ∀ x, (D.ends true).map x = (S.ends false).map x)
    (i : ∀ x, (E.ends true).map x = (T.ends false).map x)

abbrev left := D.assocLeft S h
abbrev right := E.assocRight T i
abbrev before := HorizontalAssociativity.beforeGlobe D E e
abbrev suffix := HorizontalAssociativity.suffix S T j

def midRight : OmegaCategory.Functor (K.{u} n).nu
    (Y.homCategory ((D.ends true).map (vertex n true)) ((T.ends true).map (vertex n true))) :=
  homCast T.diagonal ((h _).trans (S.horizontal_seam T j false)).symm rfl

def A := homCompose (left D S h) (S.horizontalDiagonalOne T j)
def B := homCompose (constantInterval (endGlobe D.diagonal false)) (midRight D S T j h)
def C := homCompose D.diagonal (constantInterval (endGlobe (midRight D S T j h) true))
def B' := homCompose D.diagonal (constantInterval (endGlobe (midRight D S T j h) false))
def C' := homCompose (constantInterval (endGlobe D.diagonal true)) (midRight D S T j h)
def Z := homCompose (D.horizontalDiagonalTwo E e) (right E T i)

lemma B_eq :
    B D S T j h = homCompose (left D S h) (S.horizontalDiagonalTwo T j) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map (atEnd false (project x))).val (T.diagonal.map x).val =
    Y.join 0 (D.edge false) (Y.join 0 ((S.ends false).map (suspendTable (project x))) (T.diagonal.map x).val)
  erw [D.left, h]
  apply Y.join_assoc 0
  · erw [← h]
    exact D.edge_end_matching _
  · erw [← (S.ends false).map_target]
    change (S.ends false).map (truncate 0 true (suspendTable (project x))) = _
    rw [suspend_truncate_zero, S.horizontal_seam T j]
    exact (T.diagonal.map x).property.1.symm

lemma C_eq :
    C D S T j h = homCompose (D.horizontalDiagonalOne E e) (right E T i) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map x).val (T.diagonal.map (atEnd true (project x))).val =
    Y.join 0 (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x)))) (T.edge true)
  erw [T.right, ← i]
  symm
  apply Y.join_assoc 0
  · erw [← (E.ends true).map_source]
    change _ = (E.ends true).map (truncate 0 false (suspendTable (project x)))
    rw [suspend_truncate_zero, ← D.horizontal_seam E e]
    exact (D.diagonal.map x).property.2
  · erw [i]
    exact T.end_edge_matching _

lemma B'_eq :
    B' D S T j h = homCompose (D.concatDiagonalTwo S h) (constantInterval (suffix S T j)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map x).val (T.diagonal.map (atEnd false (project x))).val =
    Y.join 0 (Y.join 0 (D.diagonal.map x).val (S.edge true)) ((T.ends true).map (suspendTable (project x)))
  rw [T.left, ← j]
  symm
  apply Y.join_assoc 0
  · erw [(S.edge_source true), ← h]
    exact (D.diagonal.map x).property.2
  · rw [j]
    exact T.edge_end_matching _

lemma C'_eq :
    C' D S T j h = homCompose (constantInterval (before D E e)) (E.concatDiagonalOne T i) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.diagonal.map (atEnd true (project x))).val (T.diagonal.map x).val =
    Y.join 0 ((D.ends false).map (suspendTable (project x))) (Y.join 0 (E.edge false) (T.diagonal.map x).val)
  rw [D.right, e]
  apply Y.join_assoc 0
  · rw [← e]
    exact D.end_edge_matching _
  · erw [E.edge_target, i]
    exact (T.diagonal.map x).property.1.symm

lemma A_eq :
    A D S T j h = homCompose (D.concatDiagonalOne S h) (constantInterval (suffix S T j)) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (D.edge false) (Y.join 0 (S.diagonal.map x).val ((T.ends true).map (suspendTable (project x)))) =
    Y.join 0 (Y.join 0 (D.edge false) (S.diagonal.map x).val) ((T.ends true).map (suspendTable (project x)))
  symm
  apply Y.join_assoc 0
  · erw [D.edge_target, h]
    exact (S.diagonal.map x).property.1.symm
  · erw [← (T.ends true).map_source]
    change _ = (T.ends true).map (truncate 0 false (suspendTable (project x)))
    rw [suspend_truncate_zero, ← S.horizontal_seam T j]
    exact (S.diagonal.map x).property.2

lemma Z_eq :
    Z D E T e i = homCompose (constantInterval (before D E e)) (E.concatDiagonalTwo T i) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change Y.join 0 (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val) (T.edge true) =
    Y.join 0 ((D.ends false).map (suspendTable (project x))) (Y.join 0 (E.diagonal.map x).val (T.edge true))
  apply Y.join_assoc 0
  · erw [← (D.ends false).map_target]
    change (D.ends false).map (truncate 0 true (suspendTable (project x))) = _
    rw [suspend_truncate_zero, D.horizontal_seam E e]
    exact (E.diagonal.map x).property.1.symm
  · erw [T.edge_source, ← i]
    exact (E.diagonal.map x).property.2

lemma AB : IntervalMatching (A D S T j h) (B D S T j h) := by
  rw [B_eq]
  exact (show IntervalMatching (left D S h) (left D S h) from fun _ => rfl).homCompose (S.horizontalDiagonal_matching T j)

lemma BC : IntervalMatching (B D S T j h) (C D S T j h) :=
  (stationary_left_matching D.diagonal).homCompose (stationary_right_matching (midRight D S T j h))

lemma CZ : IntervalMatching (C D S T j h) (Z D E T e i) := by
  rw [C_eq D E S T e j h i]
  exact (D.horizontalDiagonal_matching E e).homCompose (show IntervalMatching (right E T i) (right E T i) from fun _ => rfl)

lemma AB' : IntervalMatching (A D S T j h) (B' D S T j h) := by
  rw [A_eq, B'_eq]
  exact (D.concatDiagonal_matching S h).homCompose (constantInterval_matching (suffix S T j))

lemma BC' : IntervalMatching (B' D S T j h) (C' D S T j h) :=
  (stationary_right_matching D.diagonal).homCompose (stationary_left_matching (midRight D S T j h))

lemma CZ' : IntervalMatching (C' D S T j h) (Z D E T e i) := by
  rw [C'_eq D E S T e j h i, Z_eq]
  exact (constantInterval_matching (before D E e)).homCompose (E.concatDiagonal_matching T i)

lemma left_one_map
    (hh : ∀ x, ((D.horizontal E e).ends true).map x = ((S.horizontal T j).ends false).map x)
    (x : Table (K.{u} n)) :
    (((D.horizontal E e).concatDiagonalOne (S.horizontal T j) hh).map x).val =
      ((concatInterval (A D S T j h) (B D S T j h) (AB D S T j h)).map x).val := by
  have hm : IntervalMatching
      (homCompose (left D S h) (S.horizontalDiagonalOne T j))
      (homCompose (left D S h) (S.horizontalDiagonalTwo T j)) := by
    simpa only [A, B_eq] using AB D S T j h
  have he := concatInterval_homCompose_left (D.edge false) (D.edge_fixed false)
    (D.edge_source false) ((D.edge_target false).trans (h _))
    (S.horizontalDiagonalOne T j) (S.horizontalDiagonalTwo T j) (S.horizontalDiagonal_matching T j) hm
  simp only [show constantHom (K n).nu (D.edge false) (D.edge_fixed false) (D.edge_source false)
    ((D.edge_target false).trans (h _)) = left D S h from rfl, ← B_eq] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma left_two_map
    (hh : ∀ x, ((D.horizontal E e).ends true).map x = ((S.horizontal T j).ends false).map x)
    (x : Table (K.{u} n)) :
    (((D.horizontal E e).concatDiagonalTwo (S.horizontal T j) hh).map x).val =
      ((concatInterval (C D S T j h) (Z D E T e i) (CZ D E S T e j h i)).map x).val := by
  have hm : IntervalMatching
      (homCompose (D.horizontalDiagonalOne E e) (right E T i))
      (homCompose (D.horizontalDiagonalTwo E e) (right E T i)) := by
    simpa only [Z, C_eq D E S T e j h i] using CZ D E S T e j h i
  have he := concatInterval_homCompose_right
    (D.horizontalDiagonalOne E e) (D.horizontalDiagonalTwo E e) (D.horizontalDiagonal_matching E e)
    (T.edge true) (T.edge_fixed true) ((T.edge_source true).trans (i _).symm) (T.edge_target true) hm
  simp only [show constantHom (K n).nu (T.edge true) (T.edge_fixed true)
    ((T.edge_source true).trans (i _).symm) (T.edge_target true) = right E T i from rfl,
    ← C_eq D E S T e j h i] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma right_one_map
    (ee : (D.concat S h (intervalComposition n)).edge true = (E.concat T i (intervalComposition n)).edge false)
    (x : Table (K.{u} n)) :
    (((D.concat S h (intervalComposition n)).horizontalDiagonalOne (E.concat T i (intervalComposition n)) ee).map x).val =
      ((concatInterval (A D S T j h) (B' D S T j h) (AB' D S T j h)).map x).val := by
  have hm : IntervalMatching
      (homCompose (D.concatDiagonalOne S h) (constantInterval (suffix S T j)))
      (homCompose (D.concatDiagonalTwo S h) (constantInterval (suffix S T j))) := by
    simpa only [A_eq, B'_eq] using AB' D S T j h
  have he := concatInterval_homCompose_stationary_right
    (D.concatDiagonalOne S h) (D.concatDiagonalTwo S h) (D.concatDiagonal_matching S h) (suffix S T j) hm
  simp only [← A_eq, ← B'_eq] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma right_two_map
    (ee : (D.concat S h (intervalComposition n)).edge true = (E.concat T i (intervalComposition n)).edge false)
    (x : Table (K.{u} n)) :
    (((D.concat S h (intervalComposition n)).horizontalDiagonalTwo (E.concat T i (intervalComposition n)) ee).map x).val =
      ((concatInterval (C' D S T j h) (Z D E T e i) (CZ' D E S T e j h i)).map x).val := by
  have hm : IntervalMatching
      (homCompose (constantInterval (before D E e)) (E.concatDiagonalOne T i))
      (homCompose (constantInterval (before D E e)) (E.concatDiagonalTwo T i)) := by
    simpa only [C'_eq D E S T e j h i, Z_eq] using CZ' D E S T e j h i
  have he := concatInterval_homCompose_stationary_left (before D E e)
    (E.concatDiagonalOne T i) (E.concatDiagonalTwo T i) (E.concatDiagonal_matching T i) hm
  simp only [← C'_eq D E S T e j h i, ← Z_eq] at he
  exact (congrArg (fun Q => (Q.map x).val) he).symm

end MixedZero

lemma concat_horizontal {n : ℕ} {Y : OmegaCategory.{u}}
    (D E S T : RectangleDiagram.{u,u} n Y)
    (e : D.edge true = E.edge false) (j : S.edge true = T.edge false)
    (h : ∀ x, (D.ends true).map x = (S.ends false).map x)
    (i : ∀ x, (E.ends true).map x = (T.ends false).map x)
    (hh : ∀ x, ((D.horizontal E e).ends true).map x = ((S.horizontal T j).ends false).map x)
    (ee : (D.concat S h (intervalComposition n)).edge true = (E.concat T i (intervalComposition n)).edge false) :
    (D.horizontal E e).concat (S.horizontal T j) hh (intervalComposition n) =
      (D.concat S h (intervalComposition n)).horizontal (E.concat T i (intervalComposition n)) ee := by
  apply RectangleDiagram.ext
  · funext a
    cases a <;> rfl
  · funext a
    cases a <;> rfl
  · intro x
    open MixedZero in
    have hl := concatInterval_val_congr
      ((D.horizontal E e).concatDiagonalOne (S.horizontal T j) hh)
      ((D.horizontal E e).concatDiagonalTwo (S.horizontal T j) hh)
      ((D.horizontal E e).concatDiagonal_matching (S.horizontal T j) hh)
      (concatInterval (A D S T j h) (B D S T j h) (AB D S T j h))
      (concatInterval (C D S T j h) (Z D E T e i) (CZ D E S T e j h i))
      ((AB D S T j h).concat_left ((BC D S T j h).concat_right (CZ D E S T e j h i)))
      (left_one_map D E S T e j h hh) (left_two_map D E S T e j h i hh) x
    open MixedZero in
    have hr := concatInterval_val_congr
      ((D.concat S h (intervalComposition n)).horizontalDiagonalOne (E.concat T i (intervalComposition n)) ee)
      ((D.concat S h (intervalComposition n)).horizontalDiagonalTwo (E.concat T i (intervalComposition n)) ee)
      ((D.concat S h (intervalComposition n)).horizontalDiagonal_matching (E.concat T i (intervalComposition n)) ee)
      (concatInterval (A D S T j h) (B' D S T j h) (AB' D S T j h))
      (concatInterval (C' D S T j h) (Z D E T e i) (CZ' D E S T e j h i))
      ((AB' D S T j h).concat_left ((BC' D S T j h).concat_right (CZ' D E S T e j h i)))
      (right_one_map D E S T j h i ee) (right_two_map D E S T e j h i ee) x
    open MixedZero in
    have hfl := concatInterval_four (A D S T j h) (B D S T j h) (C D S T j h) (Z D E T e i)
      (AB D S T j h) (BC D S T j h) (CZ D E S T e j h i)
    open MixedZero in
    have hfr := concatInterval_four (A D S T j h) (B' D S T j h) (C' D S T j h) (Z D E T e i)
      (AB' D S T j h) (BC' D S T j h) (CZ' D E S T e j h i)
    open MixedZero in
    have hele : concatInterval (B D S T j h) (C D S T j h) (BC D S T j h) =
        homCompose D.diagonal (midRight D S T j h) := concatInterval_shuffle_left _ _
    open MixedZero in
    have here : concatInterval (B' D S T j h) (C' D S T j h) (BC' D S T j h) =
        homCompose D.diagonal (midRight D S T j h) := concatInterval_shuffle_right _ _
    simp only [hele] at hfl
    simp only [here] at hfr
    exact hl.trans ((congrArg (fun Q => (Q.map x).val) (hfl.trans hfr.symm)).trans hr.symm)

end RectangleDiagram

lemma concatInterval_horizontal {n : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false)))
    (j : F'.map (verticalTable (vertex n true)) = G'.map (verticalTable (vertex n false)))
    (h : IntervalMatching F F') (i : IntervalMatching G G')
    (hh : IntervalMatching (horizontalCylinder F G e) (horizontalCylinder F' G' j))
    (ee : (concatInterval F F' h).map (verticalTable (vertex n true)) =
      (concatInterval G G' i).map (verticalTable (vertex n false))) :
    concatInterval (horizontalCylinder F G e) (horizontalCylinder F' G' j) hh =
      horizontalCylinder (concatInterval F F' h) (concatInterval G G' i) ee := by
  unfold horizontalCylinder
  change (((rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor F).horizontal
    (rectangleDiagramOfFunctor G) e).lift)).concat
    (rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor F').horizontal
      (rectangleDiagramOfFunctor G') j).lift)) _ (intervalComposition n)).lift) =
      ((rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor F).concat
        (rectangleDiagramOfFunctor F') h (intervalComposition n)).lift)).horizontal
        (rectangleDiagramOfFunctor (((rectangleDiagramOfFunctor G).concat
          (rectangleDiagramOfFunctor G') i (intervalComposition n)).lift)) _).lift
  simp only [RectangleDiagram.ofFunctor_lift]
  exact congrArg RectangleDiagram.lift
    ((rectangleDiagramOfFunctor F).concat_horizontal (rectangleDiagramOfFunctor G)
      (rectangleDiagramOfFunctor F') (rectangleDiagramOfFunctor G') e j h i _ _)

lemma concatInterval_paste_zero {n : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching 0 F G) (j : FaceMatching 0 F' G')
    (h : IntervalMatching F F') (i : IntervalMatching G G') :
    concatInterval (pasteCylinder (show 0<n+1 by omega) F G e)
      (pasteCylinder (show 0<n+1 by omega) F' G' j) (h.paste (by omega) i e j) =
      pasteCylinder (show 0<n+1 by omega) (concatInterval F F' h) (concatInterval G G' i)
        (e.concat (by omega) j h i) := by
  simp only [pasteCylinder_zero]
  exact concatInterval_horizontal F G F' G' (zeroFaceMatching_seam e) (zeroFaceMatching_seam j) h i _ _
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

namespace MixedPositive
variable {n k : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching (k+1) F G) (j : FaceMatching (k+1) F' G')
    (h : IntervalMatching F F') (i : IntervalMatching G G')

abbrev A := (rectangleDiagramOfFunctor F).concatDiagonalOne (rectangleDiagramOfFunctor F') h
abbrev B := (rectangleDiagramOfFunctor F).concatDiagonalTwo (rectangleDiagramOfFunctor F') h
abbrev C := homCompose ((rectangleDiagramOfFunctor F).assocLeft (rectangleDiagramOfFunctor F') h)
  (CylinderComposition.secondDiagonal F' G' j)
abbrev Z := homCompose (CylinderComposition.secondDiagonal F G e)
  ((rectangleDiagramOfFunctor F).assocRight (rectangleDiagramOfFunctor F') h)

lemma AC : FaceMatching k (A F F' h) (C F F' G' j h) :=
  (show FaceMatching k ((rectangleDiagramOfFunctor F).assocLeft (rectangleDiagramOfFunctor F') h)
    ((rectangleDiagramOfFunctor F).assocLeft (rectangleDiagramOfFunctor F') h) from fun _ => rfl).homCompose
      (CylinderComposition.diagonal_matching F' G' j)

lemma BZ : FaceMatching k (B F F' h) (Z F G F' e h) :=
  (CylinderComposition.diagonal_matching F G e).homCompose
    (show FaceMatching k ((rectangleDiagramOfFunctor F).assocRight (rectangleDiagramOfFunctor F') h)
      ((rectangleDiagramOfFunctor F).assocRight (rectangleDiagramOfFunctor F') h) from fun _ => rfl)

lemma AB : IntervalMatching (A F F' h) (B F F' h) :=
  (rectangleDiagramOfFunctor F).concatDiagonal_matching (rectangleDiagramOfFunctor F') h

include e in
lemma C_map (x : Table (K.{u} n)) :
    ((C F F' G' j h).map x).val =
      (((rectangleDiagramOfFunctor G).concatDiagonalOne (rectangleDiagramOfFunctor G') i).map x).val := by
  change Y.join 0 (F.map (verticalTable (vertex n false))) (G'.map (up x)) =
    Y.join 0 (G.map (verticalTable (vertex n false))) (G'.map (up x))
  rw [e.edges false]

include j in
lemma Z_map (x : Table (K.{u} n)) :
    ((Z F G F' e h).map x).val =
      (((rectangleDiagramOfFunctor G).concatDiagonalTwo (rectangleDiagramOfFunctor G') i).map x).val := by
  change Y.join 0 (G.map (up x)) (F'.map (verticalTable (vertex n true))) =
    Y.join 0 (G.map (up x)) (G'.map (verticalTable (vertex n true)))
  rw [j.edges true]

include i in
lemma CZ : IntervalMatching (C F F' G' j h) (Z F G F' e h) :=
  IntervalMatching.of_val _ _ _ _
    ((rectangleDiagramOfFunctor G).concatDiagonal_matching (rectangleDiagramOfFunctor G') i)
    (C_map F G F' G' e j h i) (Z_map F G F' G' e j h i)

lemma left_one_map (hk : k < n)
    (hh : IntervalMatching (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j))
    (x : Table (K.{u} n)) :
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)).concatDiagonalOne
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j)) hh).map x).val =
      ((pasteCylinder hk (A F F' h) (C F F' G' j h) (AC F F' G' j h)).map x).val := by
  let D := rectangleDiagramOfFunctor F
  let S := rectangleDiagramOfFunctor F'
  have he := pasteCylinder_homCompose_left hk (D.edge false) (D.edge_fixed false)
    (D.edge_source false) ((D.edge_target false).trans (h _))
    S.diagonal (CylinderComposition.secondDiagonal F' G' j)
    (CylinderComposition.diagonal_matching F' G' j) (AC F F' G' j h)
  change Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F G e).map (verticalTable (vertex n false)))
    ((pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j).map (up x)) = _
  rw [pasteCylinder_succ_edge hk, pasteCylinder_succ_up hk]
  exact (congrArg (fun Q => (Q.map x).val) he).symm

lemma left_two_map (hk : k < n)
    (hh : IntervalMatching (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)
      (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j))
    (x : Table (K.{u} n)) :
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F G e)).concatDiagonalTwo
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j)) hh).map x).val =
      ((pasteCylinder hk (B F F' h) (Z F G F' e h) (BZ F G F' e h)).map x).val := by
  let D := rectangleDiagramOfFunctor F
  let S := rectangleDiagramOfFunctor F'
  have he := pasteCylinder_homCompose_right hk D.diagonal (CylinderComposition.secondDiagonal F G e)
    (CylinderComposition.diagonal_matching F G e) (S.edge true) (S.edge_fixed true)
      ((S.edge_source true).trans (h _).symm) (S.edge_target true) (BZ F G F' e h)
  change Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F G e).map (up x))
    ((pasteCylinder (Nat.add_lt_add_right hk 1) F' G' j).map (verticalTable (vertex n true))) = _
  rw [pasteCylinder_succ_edge hk, pasteCylinder_succ_up hk]
  exact (congrArg (fun Q => (Q.map x).val) he).symm

end MixedPositive

lemma concatInterval_paste (n k : ℕ) (hk : k < n) {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} n).nu Y)
    (e : FaceMatching k F G) (j : FaceMatching k F' G')
    (h : IntervalMatching F F') (i : IntervalMatching G G') :
    concatInterval (pasteCylinder hk F G e) (pasteCylinder hk F' G' j) (h.paste hk i e j) =
      pasteCylinder hk (concatInterval F F' h) (concatInterval G G' i) (e.concat (Nat.le_of_lt hk) j h i) := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n => exact concatInterval_paste_zero F G F' G' e j h i
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      apply functor_ext_rectangle
      · intro a x
        have he : endGlobe (concatInterval (pasteCylinder hk F G e) (pasteCylinder hk F' G' j)
            (h.paste hk i e j)) a = endGlobe (pasteCylinder hk (concatInterval F F' h)
            (concatInterval G G' i) (e.concat (Nat.le_of_lt hk) j h i)) a := by
          apply GlobeComplex.functor_ext
          change (concatInterval (pasteCylinder hk F G e) (pasteCylinder hk F' G' j)
            (h.paste hk i e j)).map (atEnd a (topTable (n+1))) =
              (pasteCylinder hk (concatInterval F F' h) (concatInterval G G' i)
                (e.concat (Nat.le_of_lt hk) j h i)).map (atEnd a (topTable (n+1)))
          cases a <;> simp only [concatInterval_endpoint, Bool.false_eq_true, ite_false, ite_true, pasteCylinder_endpoint_top]
        exact congrArg (fun Q => Q.map x) he
      · intro a
        rw [concatInterval_succ_edge, pasteCylinder_succ_edge hk', pasteCylinder_succ_edge hk',
          pasteCylinder_succ_edge hk', concatInterval_succ_edge]
      · intro x
        rw [concatInterval_succ_up, pasteCylinder_succ_up hk']
        open MixedPositive in
        have hl := concatInterval_val_congr
          ((rectangleDiagramOfFunctor (pasteCylinder hk F G e)).concatDiagonalOne
            (rectangleDiagramOfFunctor (pasteCylinder hk F' G' j)) (h.paste hk i e j))
          ((rectangleDiagramOfFunctor (pasteCylinder hk F G e)).concatDiagonalTwo
            (rectangleDiagramOfFunctor (pasteCylinder hk F' G' j)) (h.paste hk i e j))
          ((rectangleDiagramOfFunctor (pasteCylinder hk F G e)).concatDiagonal_matching
            (rectangleDiagramOfFunctor (pasteCylinder hk F' G' j)) (h.paste hk i e j))
          (pasteCylinder hk' (A F F' h) (C F F' G' j h) (AC F F' G' j h))
          (pasteCylinder hk' (B F F' h) (Z F G F' e h) (BZ F G F' e h))
          ((AB F F' h).paste hk' (CZ F G F' G' e j h i) (AC F F' G' j h) (BZ F G F' e h))
          (left_one_map F G F' G' e j h hk' (h.paste hk i e j))
          (left_two_map F G F' G' e j h hk' (h.paste hk i e j)) x
        open MixedPositive in
        have hi := ih n hk' (A F F' h) (C F F' G' j h) (B F F' h) (Z F G F' e h)
          (AC F F' G' j h) (BZ F G F' e h) (AB F F' h) (CZ F G F' G' e j h i)
        refine hl.trans ((congrArg (fun Q => (Q.map x).val) hi).trans ?_)
        apply pasteCylinder_val_congr hk'
        · intro z
          exact (concatInterval_succ_up F F' h z).symm
        · intro z
          change ((concatInterval (MixedPositive.C F F' G' j h) (MixedPositive.Z F G F' e h)
            (MixedPositive.CZ F G F' G' e j h i)).map z).val = (concatInterval G G' i).map (up z)
          erw [concatInterval_succ_up]
          open MixedPositive in
          exact concatInterval_val_congr _ _ _ _ _ _
            (C_map F G F' G' e j h i) (Z_map F G F' G' e j h i) z
end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma FaceMatching.of_val {n k : ℕ} {Y : OmegaCategory.{u}} {a b c d : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b))
    (F' G' : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory c d))
    (h : FaceMatching k F' G')
    (he : ∀ x, (F.map x).val = (F'.map x).val)
    (hf : ∀ x, (G.map x).val = (G'.map x).val) : FaceMatching k F G := by
  intro x
  apply Subtype.ext
  rw [he, hf]
  exact congrArg Subtype.val (h x)

lemma pasteCylinder_homCompose_stationary_right {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory a b)) (h : FaceMatching k F G)
    (P Q : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory b c))
    (hPQ : (Y.homCategory b c).target k (P.map (topTable n)) = (Y.homCategory b c).source k (Q.map (topTable n)))
    (h' : FaceMatching k (homCompose F (constantInterval P)) (homCompose G (constantInterval Q))) :
    pasteCylinder hk (homCompose F (constantInterval P)) (homCompose G (constantInterval Q)) h' =
      homCompose (pasteCylinder hk F G h) (constantInterval (globeComposite hk P Q hPQ)) := by
  have he := pasteCylinder_homCompose hk F G h (constantInterval P) (constantInterval Q)
    (constantInterval_faceMatching P Q hPQ)
  rw [pasteCylinder_constant n k hk P Q hPQ] at he
  exact he

lemma pasteCylinder_homCompose_stationary_left {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{u}} {a b c : Y.Cell}
    (P Q : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a b))
    (hPQ : (Y.homCategory a b).target k (P.map (topTable n)) = (Y.homCategory a b).source k (Q.map (topTable n)))
    (F G : OmegaCategory.Functor (K.{u} n).nu (Y.homCategory b c)) (h : FaceMatching k F G)
    (h' : FaceMatching k (homCompose (constantInterval P) F) (homCompose (constantInterval Q) G)) :
    pasteCylinder hk (homCompose (constantInterval P) F) (homCompose (constantInterval Q) G) h' =
      homCompose (constantInterval (globeComposite hk P Q hPQ)) (pasteCylinder hk F G h) := by
  have he := pasteCylinder_homCompose hk (constantInterval P) (constantInterval Q)
    (constantInterval_faceMatching P Q hPQ) F G h
  rw [pasteCylinder_constant n k hk P Q hPQ] at he
  exact he

lemma globeComposite_endpoint_val {n k : ℕ} (hk : k < n)
    {Y : OmegaCategory.{u}} {a c : Y.Cell}
    (P Q : OmegaCategory.Functor (complex.{u} n).nu (Y.homCategory a c))
    (hPQ : (Y.homCategory a c).target k (P.map (topTable n)) = (Y.homCategory a c).source k (Q.map (topTable n)))
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y) (h : FaceMatching (k+1) F G) (b : Bool)
    (hP : (P.map (topTable n)).val = F.map (atEnd b (topTable (n+1))))
    (hQ : (Q.map (topTable n)).val = G.map (atEnd b (topTable (n+1))))
    (x : Table (complex.{u} n)) :
    ((globeComposite hk P Q hPQ).map x).val =
      (pasteCylinder (Nat.add_lt_add_right hk 1) F G h).map (atEnd b (suspendTable x)) := by
  apply globeSuspended_ext _ (endGlobe (pasteCylinder (Nat.add_lt_add_right hk 1) F G h) b)
  rw [globeComposite_top, hom_join_val _ _ _ hPQ, hP, hQ]
  exact (pasteCylinder_endpoint_top (Nat.add_lt_add_right hk 1) F G h b).symm

namespace ZeroInterchange
variable {n k : ℕ} {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching 0 F G) (j : FaceMatching 0 F' G')
    (h : FaceMatching (k+1) F F') (i : FaceMatching (k+1) G G')

abbrev D := rectangleDiagramOfFunctor F
abbrev E := rectangleDiagramOfFunctor G
abbrev S := rectangleDiagramOfFunctor F'
abbrev T := rectangleDiagramOfFunctor G'

abbrev suffix := RectangleDiagram.HorizontalAssociativity.suffix (D F) (E G) (zeroFaceMatching_seam e)

def suffix' : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory (F.map (atEnd true (vertex n true))) (G.map (atEnd true (vertex n true)))) :=
  homCast (globeHomMap ((T G').ends true))
    ((i.vertices true false).symm.trans ((D F).horizontal_seam (E G) (zeroFaceMatching_seam e) true).symm)
    (i.vertices true true).symm

lemma suffix_matching :
    (Y.homCategory (F.map (atEnd true (vertex n true))) (G.map (atEnd true (vertex n true)))).target k
      ((suffix F G e).map (topTable n)) =
    (Y.homCategory (F.map (atEnd true (vertex n true))) (G.map (atEnd true (vertex n true)))).source k
      ((suffix' F G G' e i).map (topTable n)) := by
  apply Subtype.ext
  change Y.target (k+1) (G.map (atEnd true (suspendTable (topTable n)))) =
    Y.source (k+1) (G'.map (atEnd true (suspendTable (topTable n))))
  rw [suspendTable_top]
  exact i.ends true

abbrev before := RectangleDiagram.HorizontalAssociativity.beforeGlobe (D F) (E G) (zeroFaceMatching_seam e)

def before' : OmegaCategory.Functor (complex.{u} n).nu
    (Y.homCategory (F.map (atEnd false (vertex n false))) (G.map (atEnd false (vertex n false)))) :=
  homCast (globeHomMap ((S F').ends false)) (h.vertices false false).symm
    ((h.vertices false true).symm.trans ((D F).horizontal_seam (E G) (zeroFaceMatching_seam e) false))

lemma before_matching :
    (Y.homCategory (F.map (atEnd false (vertex n false))) (G.map (atEnd false (vertex n false)))).target k
      ((before F G e).map (topTable n)) =
    (Y.homCategory (F.map (atEnd false (vertex n false))) (G.map (atEnd false (vertex n false)))).source k
      ((before' F G F' e h).map (topTable n)) := by
  apply Subtype.ext
  change Y.target (k+1) (F.map (atEnd false (suspendTable (topTable n)))) =
    Y.source (k+1) (F'.map (atEnd false (suspendTable (topTable n))))
  rw [suspendTable_top]
  exact h.ends false

abbrev A := homCompose (D F).diagonal (constantInterval (suffix F G e))
abbrev C := homCompose (CylinderComposition.secondDiagonal F F' h) (constantInterval (suffix' F G G' e i))
abbrev B := homCompose (constantInterval (before F G e)) (E G).diagonal
abbrev Z := homCompose (constantInterval (before' F G F' e h)) (CylinderComposition.secondDiagonal G G' i)

lemma AC : FaceMatching k (A F G e) (C F G F' G' e h i) :=
  (CylinderComposition.diagonal_matching F F' h).homCompose
    (constantInterval_faceMatching _ _ (suffix_matching F G G' e i))

lemma BZ : FaceMatching k (B F G e) (Z F G F' G' e h i) :=
  (constantInterval_faceMatching _ _ (before_matching F G F' e h)).homCompose
    (CylinderComposition.diagonal_matching G G' i)

lemma AB : IntervalMatching (A F G e) (B F G e) :=
  (D F).horizontalDiagonal_matching (E G) (zeroFaceMatching_seam e)

include j in
lemma CZ : IntervalMatching (C F G F' G' e h i) (Z F G F' G' e h i) :=
  IntervalMatching.of_val _ _ _ _
    ((S F').horizontalDiagonal_matching (T G') (zeroFaceMatching_seam j)) (fun _ => rfl) (fun _ => rfl)

lemma paste_one_map (hk : k < n)
    (ee : FaceMatching 0 (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (x : Table (K.{u} n)) :
    ((pasteCylinder hk (A F G e) (C F G F' G' e h i) (AC F G F' G' e h i)).map x).val =
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalOne
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee)).map x).val := by
  have he := pasteCylinder_homCompose_stationary_right hk
    (D F).diagonal (CylinderComposition.secondDiagonal F F' h) (CylinderComposition.diagonal_matching F F' h)
    (suffix F G e) (suffix' F G G' e i) (suffix_matching F G G' e i) (AC F G F' G' e h i)
  erw [he]
  change Y.join 0 ((pasteCylinder hk (D F).diagonal _ _).map x).val
    ((globeComposite hk (suffix F G e) (suffix' F G G' e i) (suffix_matching F G G' e i)).map (project x)).val =
      Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F F' h).map (up x))
        ((pasteCylinder (Nat.add_lt_add_right hk 1) G G' i).map (atEnd true (suspendTable (project x))))
  rw [pasteCylinder_succ_up hk]
  congr 1
  apply globeComposite_endpoint_val hk _ _ _ G G' i true
  · exact congrArg (fun z => G.map (atEnd true z)) (suspendTable_top n)
  · exact congrArg (fun z => G'.map (atEnd true z)) (suspendTable_top n)

lemma paste_two_map (hk : k < n)
    (ee : FaceMatching 0 (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (x : Table (K.{u} n)) :
    ((pasteCylinder hk (B F G e) (Z F G F' G' e h i) (BZ F G F' G' e h i)).map x).val =
    (((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalTwo
      (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee)).map x).val := by
  have he := pasteCylinder_homCompose_stationary_left hk
    (before F G e) (before' F G F' e h) (before_matching F G F' e h)
    (E G).diagonal (CylinderComposition.secondDiagonal G G' i) (CylinderComposition.diagonal_matching G G' i)
    (BZ F G F' G' e h i)
  erw [he]
  change Y.join 0 ((globeComposite hk (before F G e) (before' F G F' e h) (before_matching F G F' e h)).map (project x)).val
    ((pasteCylinder hk (E G).diagonal _ _).map x).val =
      Y.join 0 ((pasteCylinder (Nat.add_lt_add_right hk 1) F F' h).map (atEnd false (suspendTable (project x))))
        ((pasteCylinder (Nat.add_lt_add_right hk 1) G G' i).map (up x))
  rw [pasteCylinder_succ_up hk]
  congr 1
  apply globeComposite_endpoint_val hk _ _ _ F F' h false
  · exact congrArg (fun z => F.map (atEnd false z)) (suspendTable_top n)
  · exact congrArg (fun z => F'.map (atEnd false z)) (suspendTable_top n)

end ZeroInterchange

lemma pasteCylinder_interchange_zero {n k : ℕ} (hk : k < n) {Y : OmegaCategory.{u}}
    (F G F' G' : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (e : FaceMatching 0 F G) (j : FaceMatching 0 F' G')
    (h : FaceMatching (k+1) F F') (i : FaceMatching (k+1) G G')
    (ee : FaceMatching 0 (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i))
    (hh : FaceMatching (k+1) (pasteCylinder (show 0<n+1 by omega) F G e)
      (pasteCylinder (show 0<n+1 by omega) F' G' j)) :
    pasteCylinder (show 0<n+1 by omega) (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
      (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i) ee =
    pasteCylinder (Nat.add_lt_add_right hk 1) (pasteCylinder (show 0<n+1 by omega) F G e)
      (pasteCylinder (show 0<n+1 by omega) F' G' j) hh := by
  apply functor_ext_rectangle
  · intro a x
    have he : endGlobe (pasteCylinder (show 0<n+1 by omega)
        (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)
        (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i) ee) a =
      endGlobe (pasteCylinder (Nat.add_lt_add_right hk 1)
        (pasteCylinder (show 0<n+1 by omega) F G e)
        (pasteCylinder (show 0<n+1 by omega) F' G' j) hh) a := by
      apply GlobeComplex.functor_ext
      change (pasteCylinder (by omega) _ _ ee).map (atEnd a (topTable (n+1))) =
        (pasteCylinder (by omega) _ _ hh).map (atEnd a (topTable (n+1)))
      simp only [pasteCylinder_endpoint_top]
      exact Y.join_interchange 0 (k+1) (by omega) _ _ _ _
        (h.ends a) (i.ends a) (e.ends a) (j.ends a)
    exact congrArg (fun Q => Q.map x) he
  · intro a
    rw [pasteCylinder_zero_edge, pasteCylinder_succ_edge hk]
    cases a <;> simp only [Bool.false_eq_true, ite_false, ite_true, pasteCylinder_succ_edge hk,
      pasteCylinder_zero_edge]
  · intro x
    rw [pasteCylinder_zero_up, pasteCylinder_succ_up hk]
    open ZeroInterchange in
    have hl := concatInterval_val_congr
      ((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalOne
        (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee))
      ((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonalTwo
        (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee))
      ((rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) F F' h)).horizontalDiagonal_matching
        (rectangleDiagramOfFunctor (pasteCylinder (Nat.add_lt_add_right hk 1) G G' i)) (zeroFaceMatching_seam ee))
      (pasteCylinder hk (A F G e) (C F G F' G' e h i) (AC F G F' G' e h i))
      (pasteCylinder hk (B F G e) (Z F G F' G' e h i) (BZ F G F' G' e h i))
      ((AB F G e).paste hk (CZ F G F' G' e j h i) (AC F G F' G' e h i) (BZ F G F' G' e h i))
      (fun z => (paste_one_map F G F' G' e h i hk ee z).symm)
      (fun z => (paste_two_map F G F' G' e h i hk ee z).symm) x
    open ZeroInterchange in
    have hi := concatInterval_paste n k hk (A F G e) (C F G F' G' e h i)
      (B F G e) (Z F G F' G' e h i) (AC F G F' G' e h i) (BZ F G F' G' e h i)
      (AB F G e) (CZ F G F' G' e j h i)
    refine hl.trans ((congrArg (fun Q => (Q.map x).val) hi).trans ?_)
    apply pasteCylinder_val_congr hk
    · intro z
      exact (pasteCylinder_zero_up F G e z).symm
    · intro z
      change ((concatInterval (ZeroInterchange.C F G F' G' e h i)
        (ZeroInterchange.Z F G F' G' e h i) (ZeroInterchange.CZ F G F' G' e j h i)).map z).val =
          (pasteCylinder (show 0<n+1 by omega) F' G' j).map (up z)
      erw [pasteCylinder_zero_up]
      apply concatInterval_val_congr <;> intro w <;> rfl
end Thomason.GrayRecursive

end

end OAI
