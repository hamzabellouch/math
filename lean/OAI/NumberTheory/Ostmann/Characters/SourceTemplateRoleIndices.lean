import OAI.NumberTheory.Ostmann.Characters.SourceTemplateDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Template

abbrev HalfRoleConstituent {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :=
  Σ r : InitialRole k, Fin (sourceWidth cfg m r.role)

abbrev HalfSourceCoordinates {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :=
  Fin (m+1) ⊕ (Fin (2*k) ⊕ (Σ j : Fin (k+1), Fin (cfg.2 j).length))

def pairBoolSumEquiv (α : Type*) : (α × Bool) ≃ α ⊕ α where
  toFun x := if x.2 then .inr x.1 else .inl x.1
  invFun
    | .inl a => (a,false)
    | .inr a => (a,true)
  left_inv x := by rcases x with ⟨a,b⟩; cases b <;> rfl
  right_inv x := by cases x <;> rfl

def anchorCoordinateEquiv (k : ℕ) : (Fin k × Bool) ≃ Fin (2*k) :=
  (pairBoolSumEquiv (Fin k)).trans (finSumFinEquiv.trans (finCongr (by omega)))

def anchorCoordinate {k : ℕ} (j : Fin k) (big : Bool) : Fin (2*k) :=
  anchorCoordinateEquiv k (j,big)

def halfRoleToCoordinates {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    HalfRoleConstituent cfg m → HalfSourceCoordinates cfg m
  | ⟨.word,a⟩ => .inl a
  | ⟨.anchor j b,_⟩ => .inr (.inl (anchorCoordinate j b))
  | ⟨.pivot j,a⟩ => .inr (.inr ⟨j.castSucc,Fin.cast (sourceWidth_pivot cfg m j) a⟩)
  | ⟨.filler,a⟩ => .inr (.inr ⟨Fin.last k,a⟩)

def coordinatesToHalfRole {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    HalfSourceCoordinates cfg m → HalfRoleConstituent cfg m
  | .inl a => ⟨.word,a⟩
  | .inr (.inl a) => ⟨.anchor ((anchorCoordinateEquiv k).symm a).1
      ((anchorCoordinateEquiv k).symm a).2,⟨0,by change 0 < 1; omega⟩⟩
  | .inr (.inr ⟨j,a⟩) =>
    Fin.lastCases (fun a => ⟨.filler,a⟩)
      (fun j a => ⟨.pivot j,Fin.cast (sourceWidth_pivot cfg m j).symm a⟩) j a

def halfRoleCoordinateEquiv {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    HalfRoleConstituent cfg m ≃ HalfSourceCoordinates cfg m where
  toFun := halfRoleToCoordinates cfg m
  invFun := coordinatesToHalfRole cfg m
  left_inv x := by
    rcases x with ⟨r,a⟩
    cases r with
    | word => rfl
    | pivot j =>
      simp [halfRoleToCoordinates, coordinatesToHalfRole]
      rfl
    | filler => simp [halfRoleToCoordinates, coordinatesToHalfRole]
    | anchor j b =>
      have he : (anchorCoordinateEquiv k).symm (anchorCoordinate j b) = (j,b) :=
        (anchorCoordinateEquiv k).symm_apply_apply (j,b)
      have ha : a = (⟨0,by change 0 < 1; omega⟩ : Fin (sourceWidth cfg m (InitialRole.anchor j b).role)) :=
        Fin.ext (by change a.val = 0; have hh := a.isLt; change a.val < 1 at hh; omega)
      subst a
      dsimp only [halfRoleToCoordinates, coordinatesToHalfRole]
      rw [he]
  right_inv x := by
    rcases x with a | (a | ⟨j,a⟩)
    · rfl
    · change Sum.inr (Sum.inl ((anchorCoordinateEquiv k) ((anchorCoordinateEquiv k).symm a))) = _
      rw [Equiv.apply_symm_apply]
    · refine Fin.lastCases ?_ (fun j => ?_) j a
      · intro a; simp [halfRoleToCoordinates, coordinatesToHalfRole]
      · intro a; simp [halfRoleToCoordinates, coordinatesToHalfRole]
        rfl

def constituentHalfEquiv {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    SourceConstituent cfg m ≃ HalfRoleConstituent cfg m × Bool where
  toFun x := (⟨x.1.1,x.2⟩,x.1.2)
  invFun x := ⟨(x.1.1,x.2),x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
