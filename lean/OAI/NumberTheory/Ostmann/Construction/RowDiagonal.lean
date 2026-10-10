import OAI.NumberTheory.Ostmann.Construction.CountedRows

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

def refinedRowDiagonal {α κ : Type*} [Fintype α] [DecidableEq κ]
    (w : α→ℝ) (exactTag : α→κ) (f : α→ℂ) : ℂ :=
  diagonalComplex Finset.univ exactTag (fun x => (w x:ℂ)*f x)

def refinedRowOffDiagonal {α τ κ : Type*} [Fintype α] [DecidableEq τ] [DecidableEq κ]
    (w : α→ℝ) (row : α→τ) (exactTag : α→κ) (f : α→ℂ) : ℂ :=
  ∑x,∑y,if row y=row x ∧ exactTag y≠exactTag x then
    (w x:ℂ)*(w y:ℂ)*f x*conj (f y) else 0

theorem refinedRowDiagonal_nonneg {α κ : Type*} [Fintype α] [DecidableEq κ]
    (w : α→ℝ) (exactTag : α→κ) (f : α→ℂ) :
    0≤(refinedRowDiagonal w exactTag f).re := diagonal_nonneg _ _ _

theorem refinedRowDiagonal_real {α κ : Type*} [Fintype α] [DecidableEq κ]
    (w : α→ℝ) (exactTag : α→κ) (f : α→ℂ) :
    (refinedRowDiagonal w exactTag f).im=0 := diagonal_real _ _ _

theorem refinedRow_split {α τ κ : Type*} [Fintype α] [Fintype τ]
    [DecidableEq τ] [DecidableEq κ] (w : α→ℝ) (row : α→τ) (exactTag : α→κ) (f : α→ℂ)
    (hrefine : ∀ x y, f x ≠ 0 → f y ≠ 0 → exactTag y = exactTag x → row y = row x) :
    ((∑t,‖weightedGroupedRow w row f t‖^2:ℝ):ℂ)=
      refinedRowDiagonal w exactTag f+refinedRowOffDiagonal w row exactTag f := by
  rw [weightedGroupedRow_square]
  simp only [refinedRowDiagonal,diagonalComplex,refinedRowOffDiagonal,
    ←Finset.sum_add_distrib,map_mul,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hfx : f x=0
  · simp [hfx]
  by_cases hfy : f y=0
  · simp [hfy]
  by_cases hex : exactTag y=exactTag x
  · have hr := hrefine x y hfx hfy hex
    simp only [hr,hex,ite_true,ne_eq,not_true_eq_false,and_false,ite_false,add_zero]
    ring
  · by_cases hr : row y=row x
    · simp only [hr,hex,ite_true,ite_false,ne_eq,not_false_eq_true,and_self,zero_add]
    · simp only [hr,hex,ite_false,false_and,add_zero]

end Ostmann.Construction

end

end OAI
