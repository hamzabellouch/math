import OAI.NumberTheory.Ostmann.Conclusion.HistorySelectedCovarianceCauchyActual
import OAI.NumberTheory.Ostmann.Conclusion.SelectedPermutation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion
open Construction

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem selectedCovariance_self_eq_energy
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (s l : ℕ)
    (a : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedCovariance C spectator s l a a =
      actualCoefficientEnergy C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) C.scale C.giantCenter
        (residueTransform d)
        (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l :=
  actualPermutationCovariance_self_eq_energy _ _ _ _ _ _ _ _ _ _ _ _ _ a

theorem selectedCovariance_le_identity
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (s l : ℕ)
    (a b : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedCovariance C spectator s l a b ≤ selectedCovariance C spectator s l 1 1 := by
  rw [selectedCovariance_self_eq_energy]
  exact actualPermutationCovariance_le_energy _ _ _ _ _ _ _ _ _ _ _ _ _ a b

end Ostmann.Conclusion

end

end OAI
