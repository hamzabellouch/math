import OAI.NumberTheory.Ostmann.Conclusion.ActualCovariance
import OAI.NumberTheory.Ostmann.Conclusion.BulkPositionPermutation
import OAI.NumberTheory.Ostmann.Construction.DecompositionAmplitude
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion
open Construction

@[simp] theorem two_mul_half_bulkSize (k : ℕ) (L : ℝ) :
    2*(bulkSize k L/2)=bulkSize k L := by simp [bulkSize]

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

def selectedLeafPermutation (_C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) :
    Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))) →
      Equiv.Perm (Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :=
  leafBulkPermutation (2*(bulkSize k L/2)) k l

theorem selectedLeafPermutation_source (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    C.sources ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l)[selectedLeafPermutation C l σ i].origin)=
      C.sources ((Template.current (Template.initial (2*(bulkSize k L/2)) k) l)[i].origin) := by
  unfold InitialSourceChoice.sources NominalCenterArray.sources
  exact leafBulkPermutation_source (bulkSize k L/2) k l C.bulk
    (C.cells.topSource E C.deleted_card) (C.cells.compSource E C.deleted_card) σ i

def selectedCovariance (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s l : ℕ)
    (a b : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) : ℝ :=
  actualPermutationCovariance C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) C.scale C.giantCenter
    (residueTransform d) (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l
    (selectedLeafPermutation C l) (selectedLeafPermutation_source C l) a b

theorem selectedAmplitude_sq_le_of_covariance
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (s l : ℕ)
    (hm : 0 < bulkSize k L) {R B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hreg : actualRegularEnergy C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) C.giant spectator (2*s)
      (residueTransform d) (favorableGiantResidueTransform d C.favorable) l ≤ R)
    (hbad : ∀ a b, TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s l a b ≤ B)
    (hgood : ∀ a b, ¬TransferBadArrangement (a⁻¹*b) → selectedCovariance C spectator s l a b ≤ ε) :
    ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
      C.giant spectator C.scale C.giantCenter (bulkSize k L/2) s k C.bulkBin C.spectatorBin l‖^2 ≤
      R*((((2^l : ℕ) : ℝ)^(2*(2^l : ℕ)))*
        Real.exp ((2-(3/4:ℝ)*Real.log (2^l : ℕ))*(2^l : ℕ)*(bulkSize k L : ℝ))*B+ε) := by
  have h := actualAmplitude_sq_le_of_covariance C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) C.scale C.giantCenter
    (residueTransform d) (favorableGiantResidueTransform d C.favorable)
    (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l
    (show 0 < 2^l by positivity) (show 0 < 2*(bulkSize k L/2) by simpa using hm)
    (selectedLeafPermutation C l) (selectedLeafPermutation_source C l) hB hε hreg hbad hgood
  simpa only [decompositionAmplitude,two_mul_half_bulkSize] using h

end Ostmann.Conclusion

end

end OAI
