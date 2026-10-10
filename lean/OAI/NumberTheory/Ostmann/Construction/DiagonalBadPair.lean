import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairExpansionSmall
import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairInversion
import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairSmall

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem fixedSmallCounterpartExpression_bad_le_square
    (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin))
    (B : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l)))→Prop)
    (hband : ∀e,B e→PreservesRemainingBands (Template.remainder (l+1) (Template.current seed l)) e)
    (hinv : ∀e,B e→B e.symm) :
    (∑e,if B e then fixedSmallCounterpartExpression d sources seed V giant X G bins outside l p u e
      else 0).re≤
    ∑v : AllowedFrequency V l,
      ∑z : BadCounterpartPair sources (Template.remainder (l+1) (Template.current seed l)) giant B,
        ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass z.val.1*
          (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass
            (reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant
              z.val.1 z.val.2 z.property.1)*
          diagonalSmallTerm d sources seed V giant outside l p u (z.val.1,v))*
        ‖diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (z.val.1,v)‖^2 := by
  rw [fixedSmallCounterpartExpression_badPair_re d sources seed V giant X G bins outside l p u B hband]
  apply Finset.sum_le_sum
  intro v hv
  exact diagonal_bad_pair_quadratic_bound d sources seed V giant X G bins outside l p u hsep B hinv v

theorem fixedSmallCounterpartExpression_transferBad_le_square
    (d : Decomposition) (sources : SourceFamily) (m k : ℕ)
    (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current (Template.initial m k) l)))
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current (Template.initial m k) l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current (Template.initial m k) l))[i].origin)) :
    let seed := Template.initial m k
    let T := Template.remainder (l+1) (Template.current seed l)
    let B := InitialSourceChoice.diagonalBadPermutation m k l
    (∑e,if B e then fixedSmallCounterpartExpression d sources seed V giant X G bins outside l p u e
      else 0).re≤
    ∑v : AllowedFrequency V l,∑z : BadCounterpartPair sources T giant B,
      ((remainingPrior sources T giant).mass z.val.1*
        (remainingPrior sources T giant).mass (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*
        diagonalSmallTerm d sources seed V giant outside l p u (z.val.1,v))*
      ‖diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (z.val.1,v)‖^2 := by
  apply fixedSmallCounterpartExpression_bad_le_square d sources (Template.initial m k) V giant X G bins
    outside l p u hsep (InitialSourceChoice.diagonalBadPermutation m k l)
  · intro e he
    exact he.1
  · intro e he
    exact (InitialSourceChoice.diagonalBadPermutation_symm_iff m k l e).mpr he

end Ostmann.Construction

end

end OAI
