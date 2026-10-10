import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
open Construction Construction.SourcePriorGridDeletion PrimeCellReplacement HistoryGiantPriorGrid LogCellPartition

theorem gridMean_pair_periodicTest_eq_smoothJointTestSum (G : ℝ) (E : Finset ℕ) (M : ℕ) [NeZero M]
    (R : ZMod M × ZMod M → ℂ) (hsize : (M : ℝ) < Real.exp (G-1))
    (f : (Bool → ℝ) → ℂ) :
    gridMean G E (fun p => gridMean G E (fun q =>
      R ((p : ZMod M), (q : ZMod M)) *
        f (fun t => if t then (q : ℝ) else (p : ℝ)))) =
    smoothJointTestSum (fun _ : Bool => giantPrimeCutoff G) M
      (fun _ => G-1) (fun _ => G+1) (fun _ => logCellMass G E)
      (primeTest R) (primeCutoff G f) := by
  rw [← gridMean_pair_eq_smoothJointTestSum]
  simp_rw [gridMean_eq_closedPrime_weight_sum]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [jointUnitTest_primeTest G M R hsize p q hp hq]

theorem gridMean_periodicTest_eq_mixedTest (G : ℝ) (E : Finset ℕ) (M : ℕ) [NeZero M]
    (R : ZMod M × ZMod M → ℂ) (hsize : (M : ℝ) < Real.exp (G-1))
    (n : ℤ) (f : ℕ → ℂ) :
    gridMean G E (fun p =>
      R ((n : ZMod M), (p : ZMod M))*f p) =
    gridMean G E (fun p =>
      jointUnitTest (mixedTest R (n : ZMod M))
        (fun _ : Unit => (p : ZMod M))*f p) := by
  simp_rw [gridMean_eq_closedPrime_weight_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [jointUnitTest_mixedTest G M R hsize n p hp]

theorem integer_prime_gridMean_periodicTest_eq_mixedSmoothTestSum (G : ℝ) (E : Finset ℕ) (M : ℕ) [NeZero M]
    (R : ZMod M × ZMod M → ℂ) (hsize : (M : ℝ) < Real.exp (G-1))
    (f : (Option Unit → ℝ) → ℂ) :
    (∑ n ∈ integerPivotCell G, (externalPivotWeight G n : ℂ)*
      gridMean G E (fun p =>
        R ((n : ZMod M), (p : ZMod M))*
          f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ))))) =
    mixedSmoothTestSum (giantPrimeCutoff G) (fun _ : Unit => giantPrimeCutoff G) M
      (G-1) (G+1) G smoothPartition (fun _ => G-1) (fun _ => G+1)
      (fun _ => logCellMass G E) (mixedTest R)
      (mixedGiantPrimeTest G f) := by
  rw [← integer_prime_gridMean_eq_mixedSmoothTestSum]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  simpa only [Int.cast_natCast] using gridMean_periodicTest_eq_mixedTest
    G E M R hsize (n : ℤ)
    (fun p => f (Option.elim' (n : ℝ) (fun _ : Unit => (p : ℝ))))

end Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement

end

end OAI
