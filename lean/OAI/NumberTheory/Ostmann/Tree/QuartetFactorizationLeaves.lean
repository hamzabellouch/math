import OAI.NumberTheory.Ostmann.Tree.CycleCut
import OAI.NumberTheory.Ostmann.Tree.DensityHorizontal

namespace OAI

namespace Ostmann.Tree.QuartetFactorization
noncomputable section
open scoped BigOperators
open Density
variable {F : Type*} [Field F]

def bottomCut : (k : ℕ) → Density.Cut (k+2) k
  | 0 => .stop 2
  | k+1 => .split (bottomCut k) (bottomCut k)

theorem cut_unique {d k : ℕ} (C C' : Density.Cut d k) : C = C' := by
  induction C with
  | stop d => cases C'; rfl
  | split L R ihl ihr =>
    cases C' with
    | split L' R' => rw [ihl L', ihr R']

theorem bottomCut_eq_ofLE (k : ℕ) :
    bottomCut k = Density.Cut.ofLE (by omega : k ≤ k+2) := cut_unique _ _

def bottomLeaves : (k : ℕ) → (Leaves (k+2) → Fˣ) → (Leaves k → Leaves 2 → Fˣ)
  | 0, M => fun _ => M
  | k+1, M => join (bottomLeaves k (left M)) (bottomLeaves k (right M))

def assembleBottom : (k : ℕ) → (Leaves k → Leaves 2 → Fˣ) → (Leaves (k+2) → Fˣ)
  | 0, M => M (fun i => Fin.elim0 i)
  | k+1, M => join (assembleBottom k (left M)) (assembleBottom k (right M))

theorem bottomLeaves_assemble (k : ℕ) (M : Leaves k → Leaves 2 → Fˣ) :
    bottomLeaves k (assembleBottom k M) = M := by
  induction k with
  | zero => funext v; exact congrArg M (Subsingleton.elim _ _)
  | succ k ih =>
    simp only [assembleBottom, bottomLeaves, left_join, right_join, ih, join_left_right]

theorem assemble_bottomLeaves (k : ℕ) (M : Leaves (k+2) → Fˣ) :
    assembleBottom k (bottomLeaves k M) = M := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [assembleBottom, bottomLeaves, left_join, right_join, ih, join_left_right]

def bottomLeavesEquiv (k : ℕ) :
    (Leaves (k+2) → Fˣ) ≃ (Leaves k → Leaves 2 → Fˣ) where
  toFun := bottomLeaves k
  invFun := assembleBottom k
  left_inv := assemble_bottomLeaves k
  right_inv := bottomLeaves_assemble k

theorem bottomLeaves_product (k : ℕ) (M : Leaves (k+2) → Fˣ) (v : Leaves k) :
    Parameters.leafProduct (bottomLeaves k M v) = Density.Cut.project (bottomCut k) M v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases hv : v 0 <;>
      simp only [bottomLeaves, bottomCut, Density.Cut.project, join, hv,
        Bool.false_eq_true, ↓reduceIte] <;> exact ih _ _

def bottomParameters : (k : ℕ) → Parameters F (k+2) → Leaves k → Parameters F 2
  | 0, P => fun _ => P
  | k+1, .branch _ _ _ _ L R => join (bottomParameters k L) (bottomParameters k R)

theorem bottomParameters_consistent (k : ℕ) (P : Parameters F (k+2))
    (hP : P.consistent) (v : Leaves k) : (bottomParameters k P v).consistent := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    cases P with
    | branch s a b u L R =>
      cases hv : v 0 <;> simp only [bottomParameters, join, hv, Bool.false_eq_true, ↓reduceIte]
      · exact ih L hP.2.2.1 _
      · exact ih R hP.2.2.2 _

theorem bottomParameters_bottomOpposite (k : ℕ) (P : Parameters F (k+2))
    (hP : P.bottomOpposite) (v : Leaves k) : (bottomParameters k P v).bottomOpposite := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    cases P with
    | branch s a b u L R =>
      cases hv : v 0 <;> simp only [bottomParameters, join, hv, Bool.false_eq_true, ↓reduceIte]
      · exact ih L hP.1 _
      · exact ih R hP.2 _

end
end Ostmann.Tree.QuartetFactorization

end OAI
