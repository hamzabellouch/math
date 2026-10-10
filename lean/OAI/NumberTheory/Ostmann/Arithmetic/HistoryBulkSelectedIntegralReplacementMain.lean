import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsCutoff
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIntegralReplacementMain
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement
open Construction Conclusion HistoryBulkPriorGrid HistoryPrincipalIntegralAverage
open HistoryPrincipalIntegralFinite HistoryBulkIntegralReplacement HistoryBulkGiantCorrectedBounds
open HistoryGiantPriorGrid HistorySelectedJointIntegralBounds
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prime_main_eq (L G : ℝ) (E : Finset ℕ) {N : ℕ} [NeZero N]
    (F : (ι→(ZMod N)ˣ)→ℂ) (f : (Bool→ℝ)→(ι→ℝ)→ℂ) :
    primeIntegral (fun _ : Bool=>G-1) (fun _=>G+1)
      (fun _=>Construction.logCellMass G ∅)
      (fun y=>bulkMain L E F (primeJointCutoff G f y)) =
        nestedPrimeIntegral L G E f*ResidueHaar.average F := by
  rw [primeIntegral_bulkMain]
  congr 1
  unfold nestedPrimeIntegral
  congr 1
  funext y
  dsimp only [primeCutoff,bulkIntegral]
  exact primeIntegral_const_mul _ _ _ (f y) _

theorem mixed_main_eq (L G : ℝ) (E : Finset ℕ) {N : ℕ} [NeZero N]
    (F : (ι→(ZMod N)ˣ)→ℂ) (f : (Option Unit→ℝ)→(ι→ℝ)→ℂ) :
    mixedIntegral (G-1) (G+1) G smoothPartition (fun _ : Unit=>G-1) (fun _=>G+1)
      (fun _=>Construction.logCellMass G ∅)
      (fun y=>bulkMain L E F (mixedJointCutoff G f y)) =
        nestedMixedIntegral L G E f*ResidueHaar.average F := by
  rw [mixedIntegral_bulkMain]
  congr 1
  unfold nestedMixedIntegral
  congr 1
  funext y
  dsimp only [mixedGiantPrimeTest,bulkIntegral]
  exact primeIntegral_const_mul _ _ _ (f y) _

end Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement

end

end OAI
