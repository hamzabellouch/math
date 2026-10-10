import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonSourceDefs
import OAI.NumberTheory.Ostmann.Conclusion.SelectedPermutation
import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleEnergy
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodNormalizerBasic
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalSplit

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion
open Construction Filter

def ActualSingleComparisonProvider (d : Decomposition) (Cs : ℝ) : Prop :=
    ∀ BD Bz : ℝ,0≤BD → 9≤Bz → ∀k : ℕ,2≤k →
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀(P : Finset ℕ)(hP : ∀p∈P,p.Prime)(hZ : 0<harmonicPrimeMass P)
        (E : Finset ℕ)(C : InitialSourceChoice d 200 BD Bz k L E),
        ActualComparisonSource C P hP hZ ε →
        ∀j<k,C.selectedDiagonalSingleEnergy (harmonicPrimeSource P hP hZ)
          (bulkSize k L/2) C.scale j≤
          Real.exp ((2:ℝ)^j*(initialGap 200 k L+Cs*(bulkSize k L:ℝ)))

def ActualDiagonalGoodComparisonProvider (d : Decomposition) : Prop :=
    ∀ BD Bz : ℝ,0≤BD → 9≤Bz → ∀k : ℕ,2≤k →
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀(P : Finset ℕ)(hP : ∀p∈P,p.Prime)(hZ : 0<harmonicPrimeMass P)
        (E : Finset ℕ)(C : InitialSourceChoice d 200 BD Bz k L E),
        ActualComparisonSource C P hP hZ ε →
        ∀j<k,∀e,InitialSourceChoice.diagonalGoodPermutation (2*(bulkSize k L/2)) k j e →
          ‖C.selectedDiagonalCovariance (harmonicPrimeSource P hP hZ)
            (bulkSize k L/2) C.scale j e‖≤
            Real.exp (-(selectedDiagonalGoodRate k+67*(2:ℝ)^k)*(bulkSize k L:ℝ))

def ActualBadCovarianceComparisonProvider (d : Decomposition) (Ccov : ℝ) : Prop :=
    ∀ BD Bz : ℝ,0≤BD → 9≤Bz → ∀k : ℕ,2≤k →
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀(P : Finset ℕ)(hP : ∀p∈P,p.Prime)(hZ : 0<harmonicPrimeMass P)
        (E : Finset ℕ)(C : InitialSourceChoice d 200 BD Bz k L E),
        ActualComparisonSource C P hP hZ ε →
        ∀a b,TransferBadArrangement (a⁻¹*b) →
          selectedCovariance C (harmonicPrimeSource P hP hZ) (bulkSize k L/2) k a b≤
            Real.exp ((2:ℝ)^k*(initialGap 200 k L+Ccov*(bulkSize k L:ℝ))+(bulkSize k L:ℝ))

def ActualGoodCovarianceComparisonProvider (d : Decomposition) : Prop :=
    ∀ BD Bz : ℝ,0≤BD → 9≤Bz → ∀k : ℕ,2≤k →
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀(P : Finset ℕ)(hP : ∀p∈P,p.Prime)(hZ : 0<harmonicPrimeMass P)
        (E : Finset ℕ)(C : InitialSourceChoice d 200 BD Bz k L E),
        ActualComparisonSource C P hP hZ ε →
        ∀a b,¬TransferBadArrangement (a⁻¹*b) →
          selectedCovariance C (harmonicPrimeSource P hP hZ) (bulkSize k L/2) k a b≤
            Real.exp (-(frequencyBudget 200 BD Bz k L k+65*(2:ℝ)^k*(bulkSize k L:ℝ)))

end Ostmann.Conclusion

end

end OAI
