import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingActualMatching
import OAI.NumberTheory.Ostmann.Construction.RemainingDiagonal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

theorem refinedRowDiagonal_congr_on_support {α κ τ : Type*} [Fintype α]
    [DecidableEq κ] [DecidableEq τ] (w : α→ℝ) (f : α→ℂ)
    (tag₁ : α→κ) (tag₂ : α→τ)
    (he : ∀x y,f x≠0→f y≠0→(tag₁ y=tag₁ x ↔ tag₂ y=tag₂ x)) :
    refinedRowDiagonal w tag₁ f=refinedRowDiagonal w tag₂ f := by
  unfold refinedRowDiagonal diagonalComplex
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hfx : f x=0
  · simp [hfx]
  by_cases hfy : f y=0
  · simp [hfy]
  simp only [he x y hfx hfy]

def remainingTermProductTag (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant : PrimeSource) (l : ℕ)
    (z : RemainingTerm sources seed V giant l) : ℤ×ℕ :=
  (z.2.val,remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant z.1)

theorem remainingDiagonal_eq_product_diagonal (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hlarge : ∀x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
      ∀q∈remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x,V l<q) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      (refinedRowDiagonal (remainingTermMass sources seed V giant l)
        (remainingTermProductTag sources seed V giant l)
        (remainingTermValue d P sources seed V giant X G bins outside l p u)).re := by
  unfold remainingDiagonal
  apply congrArg Complex.re
  apply refinedRowDiagonal_congr_on_support
  intro x y hx hy
  have hfx := (remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u x.1 x.2 hx).2.2.2.2
  have hfy := (remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u y.1 y.2 hy).2.2.2.2
  simpa only [remainingTermExactTag,remainingTermProductTag,Prod.mk.injEq,remainingState] using
    remainingExactTag_eq_iff sources _ giant y.1 x.1 hfy.1 hfx.1
      (fun q hq => hfy.2.trans_lt (hlarge y.1 q hq))
      (fun q hq => hfx.2.trans_lt (hlarge x.1 q hq))

theorem remainingDiagonal_eq_product_grouped_squares (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hlarge : ∀x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
      ∀q∈remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x,V l<q) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      ∑t∈Finset.univ.image (remainingTermProductTag sources seed V giant l),
        ‖groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
          (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
            remainingTermValue d P sources seed V giant X G bins outside l p u z) t‖^2 := by
  rw [remainingDiagonal_eq_product_diagonal d P sources seed V giant X G bins outside l p u hlarge]
  unfold refinedRowDiagonal
  rw [diagonal_eq_grouped_squares]
  simp only [Complex.ofReal_re]

end Ostmann.Construction

end

end OAI
