import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementStageData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainSquareValue (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l ≤ k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (mixed probability : Bool) (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) : ℂ :=
  if mixed then
    plainMixedSourceMean C (spectatorList spectator ds) σ D.reference hl
      (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      (D.admissible ds) List.length_ofFn (D.residues ds) probability
  else
    primeSourceMean C (spectatorList spectator ds) σ D.reference hl
      (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      (D.admissible ds) List.length_ofFn (D.residues ds) probability

def plainSquareAverage (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l ≤ k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed probability : Bool) : ℂ :=
  (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
    (plainSquareValue C spectator D hl σ mixed probability)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
