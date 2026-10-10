import OAI.CategoryTheory.Globular.CylinderPresentations

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet.LiftStage
variable {A X Y : GlobularSet.{v}} {p : Hom X Y} {f : Hom A Y} {m : ℕ}
theorem evalFace_app (s : LiftStage p f m) {k j : ℕ} (a : Globe.Face k j)
    (hj : j ≤ m) (hk : k ≤ m) (x : A.Cell j) :
    s.app k hk (A.evalFace a x) = X.evalFace a (s.app j hj x) := by
  cases a with
  | id => rfl
  | @face j h side =>
    change s.app k hk (A.faceMap h side x) = X.faceMap h side (s.app j hj x)
    induction j, h using Nat.le_induction with
    | base =>
      simp only [GlobularSet.faceMap_succ]
      cases side
      · exact s.source_app k hj x
      · exact s.target_app k hj x
    | succ j h ih =>
      rw [A.faceMap_source h side, X.faceMap_source h side, ← s.source_app j hj]
      exact ih (by omega) (A.source j x)
end GlobularSet.LiftStage
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] (B : GlobularFrame K)

def diskDiagram (j : ℕ) {Y : K} (a : B.obj j ⟶ Y) :
    GlobularSet.Hom (GlobularPresheaf.disk.{v} j).underlying (B.homGlob Y) where
  app k x := B.diagram.eval x.down ≫ a
  source_app k x := by
    change B.diagram.eval ((Globe.source k) ≫ x.down) ≫ a =
      B.diagram.source k ≫ B.diagram.eval x.down ≫ a
    have h := B.diagram.functor.map_comp (Globe.source k) x.down
    change B.diagram.eval _ = B.diagram.eval (Globe.source k) ≫ B.diagram.eval x.down at h
    erw [h, Category.assoc]
    congr 1
    exact CoGlobularObject.face_succ _ _ false
  target_app k x := by
    change B.diagram.eval ((Globe.target k) ≫ x.down) ≫ a =
      B.diagram.target k ≫ B.diagram.eval x.down ≫ a
    have h := B.diagram.functor.map_comp (Globe.target k) x.down
    change B.diagram.eval _ = B.diagram.eval (Globe.target k) ≫ B.diagram.eval x.down at h
    erw [h, Category.assoc]
    congr 1
    exact CoGlobularObject.face_succ _ _ true

theorem diskDiagram_cell {j : ℕ} {Y : K}
    (f : GlobularSet.Hom (GlobularPresheaf.disk.{v} j).underlying (B.homGlob Y))
    (k : ℕ) (x : (GlobularPresheaf.disk.{v} j).underlying.Cell k) :
    f.app k x = B.diagram.eval x.down ≫ f.app j ⟨𝟙 _⟩ := by
  have h := f.evalFace_app x.down ⟨𝟙 _⟩
  erw [GlobularPresheaf.underlying_evalFace] at h
  change f.app k ⟨x.down ≫ 𝟙 _⟩ = _ at h
  rw [Category.comp_id] at h
  exact h.trans (B.homGlob_eval _ _ _)

noncomputable def boundaryCell (j k : ℕ) (hk : k ≤ j) (ε : Bool) : B.obj k ⟶ B.bd (j+1) :=
  if h : k = j then eqToHom (congrArg B.obj h) ≫ (if ε then B.right j else B.left j)
  else B.diagram.face (by omega : k < j) ε ≫ B.left j

theorem boundaryCell_top (j : ℕ) (ε : Bool) :
    B.boundaryCell j j le_rfl ε = if ε then B.right j else B.left j := by
  simp only [boundaryCell, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
theorem boundaryCell_low {j k : ℕ} (h : k < j) (ε : Bool) :
    B.boundaryCell j k (by omega) ε = B.diagram.face h ε ≫ B.left j := by
  simp only [boundaryCell, dite_eq_right (show k ≠ j by omega)]
  rfl

@[reassoc] theorem boundaryCell_inc (j k : ℕ) (hk : k ≤ j) (ε : Bool) :
    B.boundaryCell j k hk ε ≫ B.inc (j+1) = B.diagram.face (by omega : k < j+1) ε := by
  by_cases h : k = j
  · subst k
    rw [B.boundaryCell_top, CoGlobularObject.face_succ]
    cases ε <;> rfl
  · have hk' : k < j := by omega
    erw [B.boundaryCell_low hk', Category.assoc]
    exact B.diagram.face_adjacent hk' ε false

theorem boundaryCell_adjacent (j k : ℕ) (hk : k+1 ≤ j) (ε δ : Bool) :
    B.diagram.adjacent k δ ≫ B.boundaryCell j (k+1) hk ε =
      B.boundaryCell j k (by omega) δ := by
  by_cases h : k+1 = j
  · subst j
    rw [B.boundaryCell_top, B.boundaryCell_low (Nat.lt_succ_self k),
      CoGlobularObject.face_succ]
    cases ε with
    | false => rfl
    | true =>
      cases δ <;> change (_ ≫ B.inc (k+1)) ≫ B.right (k+1) =
        (_ ≫ B.inc (k+1)) ≫ B.left (k+1)
      all_goals
        exact (Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (B.square (k+1)).w.symm).trans
            (Category.assoc _ _ _).symm)
  · have hk' : k+1 < j := by omega
    erw [B.boundaryCell_low hk', B.boundaryCell_low (by omega : k < j), ← Category.assoc]
    erw [← B.diagram.face_succ k δ, B.diagram.face_comp]

noncomputable def boundaryApp (j k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) : B.obj k ⟶ B.bd (j+1) := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face _ ε => exact B.boundaryCell j k hk ε

@[simp] theorem boundaryApp_face (j k : ℕ) (hk : k ≤ j) (ε : Bool) :
    B.boundaryApp j k hk ⟨Globe.Face.face (by omega : k < j+1) ε⟩ = B.boundaryCell j k hk ε := rfl

theorem boundaryApp_source (j k : ℕ) (hk : k+1 ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell (k+1)) :
    B.boundaryApp j k (by omega) ((GlobularPresheaf.disk (j+1)).underlying.source k x) =
      B.diagram.source k ≫ B.boundaryApp j (k+1) hk x := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact (B.boundaryCell_adjacent j k hk ε false).symm
theorem boundaryApp_target (j k : ℕ) (hk : k+1 ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell (k+1)) :
    B.boundaryApp j k (by omega) ((GlobularPresheaf.disk (j+1)).underlying.target k x) =
      B.diagram.target k ≫ B.boundaryApp j (k+1) hk x := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact (B.boundaryCell_adjacent j k hk ε true).symm

@[reassoc] theorem boundaryApp_inc (j k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) :
    B.boundaryApp j k hk x ≫ B.inc (j+1) = B.diagram.eval x.down := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact B.boundaryCell_inc j k hk ε

variable {D : GlobularFrame K}
namespace Hom
variable {B}
variable (e : Hom D B)
@[reassoc] theorem face_naturality {j k : ℕ} (h : j < k) (ε : Bool) :
    D.diagram.face h ε ≫ e.obj k = e.obj j ≫ B.diagram.face h ε := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [CoGlobularObject.face_succ, CoGlobularObject.face_succ]
    cases ε
    · exact e.source_naturality j
    · exact e.target_naturality j
  | succ k h ih =>
    erw [← D.diagram.face_adjacent h ε false, Category.assoc, e.source_naturality,
      ← Category.assoc, ih, Category.assoc, B.diagram.face_adjacent h ε false]
    rfl

@[reassoc] theorem boundaryCell_naturality (j k : ℕ) (hk : k ≤ j) (ε : Bool) :
    D.boundaryCell j k hk ε ≫ e.bd (j+1) = e.obj k ≫ B.boundaryCell j k hk ε := by
  by_cases h : k = j
  · subst k
    rw [D.boundaryCell_top, B.boundaryCell_top]
    cases ε
    · exact e.left j
    · exact e.right j
  · have hk' : k < j := by omega
    erw [D.boundaryCell_low hk', B.boundaryCell_low hk', Category.assoc, e.left,
      ← Category.assoc, e.face_naturality, Category.assoc]
    rfl

@[reassoc] theorem boundaryApp_naturality (j k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) :
    D.boundaryApp j k hk x ≫ e.bd (j+1) = e.obj k ≫ B.boundaryApp j k hk x := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact e.boundaryCell_naturality j k hk ε
end Hom
end GlobularFrame
end Grothendieck

end OAI
