import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleHistoryEnergy

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

def diagonalSingleXiPairComplex (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource)
    (m b s : ℕ) (X G tb td : ℝ) (l : ℕ)
    (c₁ c₂ : HistoryChoices sources seed V l) : ℂ :=
  (spectatorPrior spectator m).cmean (fun ds =>
    (assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).cmean (fun u =>
      ∑p∈integerPivotCell G,(externalPivotWeight G p:ℂ)*
        (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).cmean (fun x =>
          ∑v : AllowedFrequency V l,
            (diagonalSmallTerm d sources seed V giant (spectatorList spectator ds) l p u (x,v):ℂ)*
              (((choicesMass sources seed V l c₁*choicesMass sources seed V l c₂:ℝ):ℂ)*
                supportedHistoryPairXi d V (spectatorList spectator ds) b s X tb td G
                  (decodeHistory sources seed V l
                    (remainingState sources (Template.current seed l) (l+1) giant p u x v.val) c₁)
                  (decodeHistory sources seed V l
                    (remainingState sources (Template.current seed l) (l+1) giant p u x v.val) c₂)))))

theorem diagonalSingleXiPairComplex_re (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource)
    (m b s : ℕ) (X G tb td : ℝ) (l : ℕ)
    (c₁ c₂ : HistoryChoices sources seed V l) :
    (diagonalSingleXiPairComplex d sources seed V giant spectator m b s X G tb td l c₁ c₂).re=
      diagonalSingleXiPair d sources seed V giant spectator m b s X G tb td l c₁ c₂ := by
  simp only [diagonalSingleXiPairComplex,diagonalSingleXiPair,
    FinitePrior.mean,FinitePrior.cmean,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem diagonalSingleEnergy_eq_complex_Xi_pairs (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant spectator : PrimeSource)
    (m b s : ℕ) (X G tb td : ℝ) (l : ℕ) :
    diagonalSingleEnergy d sources seed V giant spectator m X G
      (Arithmetic.sourceStateBins b s tb td) l=
      (∑c₁ : HistoryChoices sources seed V l,∑c₂ : HistoryChoices sources seed V l,
        diagonalSingleXiPairComplex d sources seed V giant spectator m b s X G tb td l c₁ c₂).re := by
  rw [diagonalSingleEnergy_eq_Xi_pairs d sources seed V giant spectator m b s X G tb td l]
  simp only [Complex.re_sum,diagonalSingleXiPairComplex_re]

end Ostmann.Construction

end

end OAI
