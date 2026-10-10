import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridResidues

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction Construction.SourcePriorGridDeletion PrimeCellReplacement HistorySignedResidues
open LogCellPartition

theorem gridMean_liftedResidueTest_eq_mixedTest {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (G : ℝ) (E : Finset ℕ) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (hsize : (M : ℝ) < Real.exp (G-1))
    (n : ℤ) (f : ℕ → ℂ) :
    gridMean G E (fun p =>
      liftedResidueTest g V outside h k M hd ((n : ZMod M), (p : ZMod M))*f p) =
    gridMean G E (fun p =>
      jointUnitTest (mixedResidueTest g V outside h k M hd (n : ZMod M))
        (fun _ : Unit => (p : ZMod M))*f p) := by
  simp_rw [gridMean_eq_closedPrime_weight_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [jointUnitTest_mixedResidueTest g V outside h k G M hd hsize n p hp]

theorem integer_prime_gridMean_liftedResidueTest_eq_mixedSmoothTestSum {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (G : ℝ) (E : Finset ℕ) (M : ℕ) [NeZero M]
    (hd : pairModulus h k outside ∣ M) (hsize : (M : ℝ) < Real.exp (G-1))
    (f : (Option Unit → ℝ) → ℂ) :
    (∑ n ∈ integerPivotCell G, (externalPivotWeight G n : ℂ)*
      gridMean G E (fun p =>
        liftedResidueTest g V outside h k M hd ((n : ZMod M), (p : ZMod M))*
          f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ))))) =
    mixedSmoothTestSum (giantPrimeCutoff G) (fun _ : Unit => giantPrimeCutoff G) M
      (G-1) (G+1) G smoothPartition (fun _ => G-1) (fun _ => G+1)
      (fun _ => logCellMass G E) (mixedResidueTest g V outside h k M hd)
      (mixedGiantPrimeTest G f) := by
  rw [← integer_prime_gridMean_eq_mixedSmoothTestSum]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  simpa only [Int.cast_natCast] using gridMean_liftedResidueTest_eq_mixedTest
    g V outside h k G E M hd hsize (n : ℤ)
    (fun p => f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ))))

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
