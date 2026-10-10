import OAI.LinearAlgebra.MatrixMultiplication.Completion.Labels
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialRestriction

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionTermination

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
attribute [local instance] Classical.propDecidable Classical.decEq

universe uCoord
variable {X Y Z : Type uCoord}

def tensor (S : FlaggedTensor X Y Z) (deleted : Color) : Tensor ℂ X Y Z :=
  fun x y z => if ownerFlag S deleted (coordinate (x, y, z) deleted) then 0
    else S.tensor x y z

theorem support_iff (S : FlaggedTensor X Y Z) (deleted : Color) (x y z) :
    tensor S deleted x y z ≠ 0 ↔ S.tensor x y z ≠ 0 ∧
      ¬ ownerFlag S deleted (coordinate (x, y, z) deleted) := by
  by_cases h : ownerFlag S deleted (coordinate (x, y, z) deleted) <;>
    simp [tensor, h]

def leftMap (S : FlaggedTensor X Y Z) (deleted : Color) : X → X → ℂ :=
  diagonalMap (fun x => if deleted = .B ∧ S.flagB x then 0 else 1)

def middleMap (S : FlaggedTensor X Y Z) (deleted : Color) : Y → Y → ℂ :=
  diagonalMap (fun y => if deleted = .C ∧ S.flagC y then 0 else 1)

def rightMap (S : FlaggedTensor X Y Z) (deleted : Color) : Z → Z → ℂ :=
  diagonalMap (fun z => if deleted = .A ∧ S.flagA z then 0 else 1)

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restriction (S : FlaggedTensor X Y Z) (deleted : Color) :
    Tensor.restrict (leftMap S deleted) (middleMap S deleted) (rightMap S deleted)
      S.tensor = tensor S deleted := by
  funext x y z
  rw [leftMap, middleMap, rightMap, restrict_diagonal]
  cases deleted <;> simp [tensor, ownerFlag, coordinate, ite_mul, reduceCtorEq] <;> rfl

def approximation (S : FlaggedTensor X Y Z) (deleted : Color) {R d D : ℕ}
    (W : Tensor.PolynomialApproximation S.tensor R d D) :
    Tensor.PolynomialApproximation (tensor S deleted) R d D := by
  simpa only [restriction] using
    W.restrict (leftMap S deleted) (middleMap S deleted) (rightMap S deleted)

def Leaf (S : FlaggedTensor X Y Z) (deleted : Color) :=
  {p : X × Y × Z // tensor S deleted p.1 p.2.1 p.2.2 ≠ 0}

instance leafFintype (S : FlaggedTensor X Y Z) (deleted : Color) :
    Fintype (Leaf S deleted) :=
  inferInstanceAs (Fintype {p : X × Y × Z // tensor S deleted p.1 p.2.1 p.2.2 ≠ 0})

def leafEquiv (S : FlaggedTensor X Y Z) (deleted : Color) :
    Leaf S deleted ≃ {a : CompletionLabels.Leaf S // leafColor S a ≠ deleted} where
  toFun a :=
    ⟨⟨a.val, ((support_iff S deleted _ _ _).mp a.property).1⟩,
      fun h => ((support_iff S deleted _ _ _).mp a.property).2
        ((leafColor_eq_iff S _ deleted).mp h)⟩
  invFun a :=
    ⟨a.val.val, (support_iff S deleted _ _ _).mpr
      ⟨a.val.property, fun h => a.property ((leafColor_eq_iff S _ deleted).mpr h)⟩⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl

def retainedLeafEquiv (S : FlaggedTensor X Y Z) (deleted first second : Color)
    (colors : ∀ c : Color, c ≠ deleted ↔ c = first ∨ c = second) :
    Leaf S deleted ≃ RetainedLeaf S first second :=
  (leafEquiv S deleted).trans
    (Equiv.subtypeEquivRight (fun a => colors (leafColor S a)))

omit [Fintype X] [Fintype Y] [Fintype Z] in
@[simp] theorem retainedLeafEquiv_coordinates
    (S : FlaggedTensor X Y Z) (deleted first second : Color)
    (colors : ∀ c : Color, c ≠ deleted ↔ c = first ∨ c = second)
    (a : Leaf S deleted) :
    ((retainedLeafEquiv S deleted first second colors a).val).val = a.val := rfl

end MatrixMultiplication.CompletionTermination

end

end OAI
