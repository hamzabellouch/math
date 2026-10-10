import Mathlib

namespace OAI

section

section
open CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ConnectedProduct

variable (X Y : SSet)
def pairLeft (y : Y.obj (op ⦋0⦌)) : X ⟶ X ⊗ Y :=
  CartesianMonoidalCategory.lift (𝟙 X) (SSet.const y)
def pairRight (x : X.obj (op ⦋0⦌)) : Y ⟶ X ⊗ Y :=
  CartesianMonoidalCategory.lift (SSet.const x) (𝟙 Y)
lemma const_zero {X Y : SSet} (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) :
    (SSet.const (X:=X) y).app (op ⦋0⦌) x=y := by
  change Y.map _ y=y
  rw [Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 _)]
  simp
lemma pairLeft_zero (y : Y.obj (op ⦋0⦌)) (x : X.obj (op ⦋0⦌)) :
    (pairLeft X Y y).app (op ⦋0⦌) x=(x,y) := by
  change (x,(SSet.const y).app (op ⦋0⦌) x)=(x,y)
  rw [const_zero]
lemma pairRight_zero (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) :
    (pairRight X Y x).app (op ⦋0⦌) y=(x,y) := by
  change ((SSet.const x).app (op ⦋0⦌) y,y)=(x,y)
  rw [const_zero]
instance connected_tensor [X.IsConnected] [Y.IsConnected] : (X⊗Y).IsConnected where
  allEq u v := by
    obtain ⟨⟨x,y⟩,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨⟨x',y'⟩,rfl⟩ := SSet.π₀.mk_surjective v
    have h₁ := congrArg (SSet.mapπ₀ (pairLeft X Y y))
      (Subsingleton.elim (SSet.π₀.mk x) (SSet.π₀.mk x'))
    have h₂ := congrArg (SSet.mapπ₀ (pairRight X Y x'))
      (Subsingleton.elim (SSet.π₀.mk y) (SSet.π₀.mk y'))
    simp only [SSet.mapπ₀_mk,pairLeft_zero,pairRight_zero] at h₁ h₂
    exact h₁.trans h₂
  nonempty := ⟨(Classical.arbitrary _,Classical.arbitrary _)⟩
end ConnectedProduct

end

end

end OAI
