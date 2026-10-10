import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridResidues

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction Construction.SourcePriorGridDeletion PrimeCellReplacement HistorySignedResidues

theorem gridMean_pair_liftedResidueTest_eq_smoothJointTestSum {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (G : ℝ) (E : Finset ℕ) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (hsize : (M : ℝ) < Real.exp (G-1))
    (f : (Bool → ℝ) → ℂ) :
    gridMean G E (fun p => gridMean G E (fun q =>
      liftedResidueTest g V outside h k M hd ((p : ZMod M), (q : ZMod M)) *
        f (fun t => if t then (q : ℝ) else (p : ℝ)))) =
    smoothJointTestSum (fun _ : Bool => giantPrimeCutoff G) M
      (fun _ => G-1) (fun _ => G+1) (fun _ => logCellMass G E)
      (primeResidueTest g V outside h k M hd) (primeCutoff G f) := by
  rw [← gridMean_pair_eq_smoothJointTestSum]
  simp_rw [gridMean_eq_closedPrime_weight_sum]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [jointUnitTest_primeResidueTest g V outside h k G M hd hsize p q hp hq]

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
