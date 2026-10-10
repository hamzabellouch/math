import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBins
import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.FavorableGiant

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

def decompositionCoefficient (d : Decomposition) (sources : SourceFamily) (V : ℕ → ℕ)
    (X G : ℝ) (b s k : ℕ) (tb td : ℝ) (outside : List ℕ) (l : ℕ) (a : State) : ℂ :=
  actualCoefficient sources (Template.initial (2*b) k) V X G (residueTransform d)
    (Arithmetic.sourceStateBins b s tb td) outside l a

def decompositionAmplitude (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (X G : ℝ) (b s k : ℕ) (tb td : ℝ) (l : ℕ) : ℂ :=
  actualAmplitude sources (Template.initial (2*b) k) V giant spectator (2*s) X G
    (residueTransform d) (favorableGiantResidueTransform d P) (Arithmetic.sourceStateBins b s tb td) l

theorem decompositionCoefficient_zero_frequency (d : Decomposition) (sources : SourceFamily)
    (V : ℕ → ℕ) (X G : ℝ) (b s k : ℕ) (tb td : ℝ) (outside : List ℕ)
    (l : ℕ) (a : State) (ha : a.frequency=0) :
    decompositionCoefficient d sources V X G b s k tb td outside l a=0 :=
  actualCoefficient_zero_frequency _ _ _ _ _ _ _ _ _ _ ha

end Ostmann.Construction

end

end OAI
