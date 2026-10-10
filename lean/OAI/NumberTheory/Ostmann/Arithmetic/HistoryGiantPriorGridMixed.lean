import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridMixedInteger
import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorGrid
open Construction Construction.SourcePriorGridDeletion PrimeCellReplacement LogCellPartition
open scoped BigOperators

def mixedGiantPrimeTest (G : ℝ) (f : (Option Unit → ℝ) → ℂ)
    (x : Option Unit → ℝ) : ℂ :=
  (smoothPartition (Real.log (x (some ()))-G):ℂ)*f x

def giantPrimeUnitEquiv (G : ℝ) :
    PrimeCellTuple (fun _ : Unit => giantPrimeCutoff G) (fun _ => G-1) (fun _ => G+1) ≃
      {p : ℕ // p ∈ giantPrimeSupport G} :=
  Equiv.funUnique Unit _

@[simp] theorem giantPrimeUnitEquiv_apply (G : ℝ)
    (p : PrimeCellTuple (fun _ : Unit => giantPrimeCutoff G) (fun _ => G-1) (fun _ => G+1)) :
    giantPrimeUnitEquiv G p = p () := rfl

theorem integer_prime_gridMean_eq_mixedSmoothTestSum (G : ℝ) (E : Finset ℕ)
    (M : ℕ) [NeZero M] (F : ZMod M → (Unit → (ZMod M)ˣ) → ℂ)
    (f : (Option Unit → ℝ) → ℂ) :
    (∑ n ∈ integerPivotCell G, (externalPivotWeight G n:ℂ)*
      gridMean G E (fun q => jointUnitTest (F (n:ZMod M)) (fun _ : Unit => (q:ZMod M))*
        f (Option.elim' (n:ℝ) (fun _ : Unit => (q:ℝ))))) =
      mixedSmoothTestSum (giantPrimeCutoff G) (fun _ : Unit => giantPrimeCutoff G) M
        (G-1) (G+1) G smoothPartition (fun _ => G-1) (fun _ => G+1)
        (fun _ => logCellMass G E) F (mixedGiantPrimeTest G f) := by
  classical
  rw [integerPivot_weighted_sum_eq_closed]
  unfold mixedSmoothTestSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [gridMean_eq_closedPrime_subtype,Finset.mul_sum]
  rw [← (giantPrimeUnitEquiv G).sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  have hpconst (i : Unit) : p i = p () := congrArg p (Subsingleton.elim _ _)
  simp only [giantPrimeUnitEquiv_apply,hpconst,Finset.univ_unique,
    Finset.prod_singleton,mixedGiantPrimeTest,Option.elim'_some,externalPivotWeight]
  ring

end Ostmann.Arithmetic.HistoryGiantPriorGrid

end

end OAI
