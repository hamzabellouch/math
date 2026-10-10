import OAI.NumberTheory.Ostmann.Construction.ActualTransfer
import OAI.NumberTheory.Ostmann.Construction.DecompositionAmplitude
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportFrequency
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBoundsFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Conclusion
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k L/2)

theorem offDiagonal_eq_of_prime_bounds (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s l : ℕ) (hl : l<k)
    (hL : 20+10*(k:ℝ)+Real.log 2≤Real.sqrt (bulkSize k L)) (X : ℝ)
    (hprime : ∀j≤k,C.giant.AboveFrequency (frequencyBound Bs BD Bz k L j) ∧
      ∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j)) :
    extendedOffDiagonal d C.favorable C.sources (Template.initial (2*b₀) k)
      (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
      (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin) l=
    decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
      C.giant spectator X C.giantCenter b₀ s k C.bulkBin C.spectatorBin (l+1) := by
  apply extendedOffDiagonal_eq_actualAmplitude
  · exact initial_seed_types_pos _ _
  · intro x hx j hj
    change C.giant.law.mass x.1*(assignmentPrior C.sources _).mass x.2≠0 at hx
    exact (hprime j (by omega)).1 x.1 (mul_ne_zero_iff.mp hx).1
  · intro x hx q hq
    change C.giant.law.mass x.1*(assignmentPrior C.sources _).mass x.2≠0 at hx
    exact sourceMass_value_gt (hprime (l+1) (by omega)).2
      (assignedSlots_source_mass_ne_zero C.sources _ x.2 (mul_ne_zero_iff.mp hx).2 q hq)
  · intro outside u hu x y hx hy v w p hp r heq hF
    exact C.pivotPairWeight_frequency_cutoff s l hl hL X outside u x y v w hu hx hy p hp r heq hF

theorem transfer_of_prime_bounds (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s l : ℕ) (hl : l<k)
    (hL : 20+10*(k:ℝ)+Real.log 2≤Real.sqrt (bulkSize k L)) (X : ℝ)
    (hprime : ∀j≤k,C.giant.AboveFrequency (frequencyBound Bs BD Bz k L j) ∧
      ∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j)) :
    Real.exp (Real.log (logCellMass C.giantCenter ∅))*
      ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
        C.giant spectator X C.giantCenter b₀ s k C.bulkBin C.spectatorBin l‖^2≤
      extendedDiagonal d C.favorable C.sources (Template.initial (2*b₀) k)
        (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
        (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin) l+
      ‖decompositionAmplitude d C.favorable C.sources (frequencyBound Bs BD Bz k L)
        C.giant spectator X C.giantCenter b₀ s k C.bulkBin C.spectatorBin (l+1)‖ := by
  exact actualAmplitude_transfer_of_offDiagonal d C.favorable C.sources (Template.initial (2*b₀) k)
    (frequencyBound Bs BD Bz k L) spectator (2*s) X C.giantCenter C.giantPositive
    (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin) l
    (C.offDiagonal_eq_of_prime_bounds spectator s l hl hL X hprime)

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
