import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSelectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def originalSourceAverage (spectator : PrimeSource)
    (F : (Fin (2*(bulkSize k L/2))→spectator.Sample) → SelectedNonbulkSample C l →
      Draws C (l:=l) → Draws C (l:=l) →
      Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → ℂ) : ℂ :=
  (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
    (selectedNonbulkPrior C l).cmean (fun a =>
      (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).cmean (fun x =>
        (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).cmean (fun y =>
          ∑ i, F ds a x y i))))

theorem spectator_mass_ne_zero (spectator : PrimeSource)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
    (h : (spectatorPrior spectator (2*(bulkSize k L/2))).mass ds≠0) :
    ∀i,spectator.law.mass (ds i)≠0 := by
  change (∏i,spectator.law.mass (ds i))≠0 at h
  exact fun i=>Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
