import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBound
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexFixed

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

private theorem finite_triple_sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α→β→γ→ℂ) : (∑a,∑b,∑c,F a b c)=∑c,∑a,∑b,F a b c := by
  calc
    _ = ∑a,∑c,∑b,F a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

section
variable (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))

def fixedSmallCounterpartExpression
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l)))) : ℂ :=
  ∑x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
    ∑v : AllowedFrequency V l,
      ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x:ℂ)*
      (diagonalSmallTerm d sources seed V giant outside l p u (x,v):ℂ)*
      diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (x,v)*
      conj (fixedCounterpartTerm sources (Template.remainder (l+1) (Template.current seed l)) giant x
        (fun y => diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (y,v)) e)

theorem smallTransformCounterpartPairing_eq_fixed_sum :
    smallTransformCounterpartPairing d sources seed V giant X G bins outside l p u =
      (∑e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l))),
        fixedSmallCounterpartExpression d sources seed V giant X G bins outside l p u e).re := by
  unfold smallTransformCounterpartPairing fixedSmallCounterpartExpression
  simp_rw [bandCounterpartSum_eq_fixed,map_sum,Finset.mul_sum]
  apply congrArg Complex.re
  exact finite_triple_sum_rotate _

theorem remainingDiagonal_le_fixed_counterpart_sum (P : Finset ℕ)
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hsep : RemainingBandsSeparated sources (Template.remainder (l+1) (Template.current seed l)) giant) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u ≤
      (∑e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l))),
        fixedSmallCounterpartExpression d sources seed V giant X G bins outside l p u e).re := by
  rw [←smallTransformCounterpartPairing_eq_fixed_sum d sources seed V giant X G bins outside l p u]
  exact remainingDiagonal_le_small_counterpart_pairing d sources seed V giant X G bins outside l p u P hg hs hsep

end
end Ostmann.Construction

end

end OAI
