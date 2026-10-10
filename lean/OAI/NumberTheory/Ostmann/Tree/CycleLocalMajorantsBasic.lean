import OAI.NumberTheory.Ostmann.Tree.CycleQuartetActionsClassification
import OAI.NumberTheory.Ostmann.Tree.QuartetLocal
import OAI.NumberTheory.Ostmann.Tree.QuartetRemainingMeans

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.CycleQuartet
open Quartet Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]
local instance cycleLocalMajorantCharDecEq : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

def bottomSign (P : Parameters (ZMod p) 2) (side freeRight : Bool) : Bool :=
  match P with
  | .branch _ _ _ _ L R => parameterSign (if side then R else L) freeRight

def orientedCharacter (inverse : Bool) (ρ : MulChar (ZMod p) ℂ) : MulChar (ZMod p) ℂ :=
  if inverse then ρ⁻¹ else ρ

def selectedMajorant (P : Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (κ : Kind) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  match κ with
  | .same side inverse => FiniteField.sameLocalMajorant g
      (bottomSign P side false) (bottomSign P (!side) false) side (orientedCharacter inverse ρ) y
  | .cross a b inverse => FiniteField.crossLocalMajorant g
      (bottomSign P false a) (bottomSign P true b) a b (orientedCharacter inverse ρ) y

def unselectedMajorant (P : Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  if ρ=1 then FiniteField.untouchedLocalMajorant g (bottomSign P false false)
    (bottomSign P true false) y else 0

theorem selectedMajorant_nonneg (P : Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (κ : Kind) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0≤ selectedMajorant P g κ ρ y := by
  cases κ with
  | same side inverse => exact FiniteField.sameLocalMajorant_nonneg _ _ _ _ _ _
  | cross a b inverse => exact FiniteField.crossLocalMajorant_nonneg _ _ _ _ _ _ _

theorem unselectedMajorant_nonneg (P : Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) : 0≤ unselectedMajorant P g ρ y := by
  unfold unselectedMajorant
  split_ifs
  · exact FiniteField.untouchedLocalMajorant_nonneg _ _ _ _
  · exact le_rfl

theorem selectedMajorant_mean_small (P : Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (κ : Kind) (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    unitMean (selectedMajorant P g κ ρ)≤25600*treeError g := by
  cases κ with
  | same side inverse =>
    exact (FiniteField.sameLocalMajorant_mean_small _ _ _ _ _ hg0 hg).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (treeError_nonneg g))
  | cross a b inverse => exact FiniteField.crossLocalMajorant_mean_small _ _ _ _ _ _ hg0 hg

omit [Fact p.Prime] in
theorem sum_orientedCharacter (inverse : Bool) (H : MulChar (ZMod p) ℂ → ℝ) :
    (∑ ρ : MulChar (ZMod p) ℂ,H (orientedCharacter inverse ρ)) = ∑ ρ : MulChar (ZMod p) ℂ,H ρ := by
  cases inverse
  · rfl
  · exact (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp H

theorem selectedMajorant_mean_total (P : Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (κ : Kind) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ ρ : MulChar (ZMod p) ℂ,unitMean (selectedMajorant P g κ ρ))≤256 := by
  cases κ with
  | same side inverse =>
    change (∑ ρ : MulChar (ZMod p) ℂ,unitMean (FiniteField.sameLocalMajorant g
      (bottomSign P side false) (bottomSign P (!side) false) side (orientedCharacter inverse ρ)))≤256
    rw [sum_orientedCharacter inverse (fun ρ => unitMean (FiniteField.sameLocalMajorant g
      (bottomSign P side false) (bottomSign P (!side) false) side ρ))]
    exact FiniteField.sameLocalMajorant_mean_total _ _ _ _ hg0 hg
  | cross a b inverse =>
    change (∑ ρ : MulChar (ZMod p) ℂ,unitMean (FiniteField.crossLocalMajorant g
      (bottomSign P false a) (bottomSign P true b) a b (orientedCharacter inverse ρ)))≤256
    rw [sum_orientedCharacter inverse (fun ρ => unitMean (FiniteField.crossLocalMajorant g
      (bottomSign P false a) (bottomSign P true b) a b ρ))]
    exact (FiniteField.crossLocalMajorant_mean_total _ _ _ _ _ hg0 hg).trans (by norm_num)

theorem unselectedMajorant_mean_total (P : Parameters (ZMod p) 2) (g : ZMod p → ℂ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ ρ : MulChar (ZMod p) ℂ,unitMean (unselectedMajorant P g ρ))≤256 := by
  classical
  have he (ρ : MulChar (ZMod p) ℂ) : unitMean (unselectedMajorant P g ρ) =
      if ρ=1 then unitMean (FiniteField.untouchedLocalMajorant g (bottomSign P false false)
        (bottomSign P true false)) else 0 := by
    by_cases hρ : ρ=1 <;> simp [unselectedMajorant,hρ,unitMean]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact (FiniteField.untouchedLocalMajorant_mean _ _ _ hg0 hg).trans (by norm_num)

theorem selectedMajorant_same_node (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (side inverse : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    selectedMajorant N.parameters g (.same side inverse) ρ y =
      N.sameLocalMajorant g side (orientedCharacter inverse ρ) y := by
  cases side <;> rfl

theorem selectedMajorant_cross_node (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (a b inverse : Bool) (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    selectedMajorant N.parameters g (.cross a b inverse) ρ y =
      N.crossLocalMajorant g a b (orientedCharacter inverse ρ) y := by
  simp only [selectedMajorant, bottomSign, NodeInput.parameters, Bool.false_eq_true,
    ↓reduceIte, FiniteField.crossLocalMajorant, NodeInput.crossLocalMajorant,
    norm_div, Complex.norm_natCast]

theorem unselectedMajorant_node (N : NodeInput (ZMod p) 1) (g : ZMod p → ℂ)
    (ρ : MulChar (ZMod p) ℂ) (y : ZMod p) :
    unselectedMajorant N.parameters g ρ y = if ρ=1 then N.untouchedLocalMajorant g y else 0 := rfl

end Ostmann.Tree.CycleQuartet
end

end OAI
