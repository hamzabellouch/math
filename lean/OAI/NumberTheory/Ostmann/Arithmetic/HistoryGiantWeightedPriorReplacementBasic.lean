import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorCollision
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridResidues

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
open Construction HistorySignedResidues HistoryGiantPriorGrid PrimeCellReplacement

def primeTest {M : ℕ} (R : ZMod M × ZMod M → ℂ) (u : Bool → (ZMod M)ˣ) : ℂ :=
  R ((u false : ZMod M),(u true : ZMod M))

def mixedTest {M : ℕ} (R : ZMod M × ZMod M → ℂ) (r : ZMod M)
    (u : Unit → (ZMod M)ˣ) : ℂ := R (r,(u () : ZMod M))

def periodicSourcePrimeMean (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (M : ℕ) (R : ZMod M × ZMod M → ℂ) (f : (Bool → ℝ) → ℂ) : ℂ :=
  (logCellPrimeSource G E hZ).law.cmean (fun p =>
    (logCellPrimeSource G E hZ).law.cmean (fun q =>
      R (p.val,q.val)*f (fun t => if t then (q.val : ℝ) else (p.val : ℝ))))

def periodicSourceMixedMean (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (M : ℕ) (R : ZMod M × ZMod M → ℂ) (f : (Option Unit → ℝ) → ℂ) : ℂ :=
  ∑ n ∈ integerPivotCell G, (externalPivotWeight G n : ℂ)*
    (logCellPrimeSource G E hZ).law.cmean (fun q =>
      R (n,q.val)*f (Option.elim' (n : ℝ) (fun _ : Unit => (q.val : ℝ))))

def guardedPeriodicSourcePrimeMean (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (M : ℕ) (R : ZMod M × ZMod M → ℂ) (f : (Bool → ℝ) → ℂ) : ℂ :=
  (logCellPrimeSource G E hZ).law.cmean (fun p =>
    (logCellPrimeSource G E hZ).law.cmean (fun q =>
      if Nat.Coprime p.val q.val then
        R (p.val,q.val)*f (fun t => if t then (q.val : ℝ) else (p.val : ℝ)) else 0))

def guardedPeriodicSourceMixedMean (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (M : ℕ) (R : ZMod M × ZMod M → ℂ) (f : (Option Unit → ℝ) → ℂ) : ℂ :=
  ∑ n ∈ integerPivotCell G, (externalPivotWeight G n : ℂ)*
    (logCellPrimeSource G E hZ).law.cmean (fun q =>
      if Nat.Coprime n q.val then
        R (n,q.val)*f (Option.elim' (n : ℝ) (fun _ : Unit => (q.val : ℝ))) else 0)

def weightedResidueTest {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ)
    (outside : List ℕ) (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) (z : ZMod M × ZMod M) : ℂ :=
  W z*liftedResidueTest g V outside h k M hd z

theorem jointUnitTest_primeTest (G : ℝ) (M : ℕ) [NeZero M]
    (R : ZMod M × ZMod M → ℂ) (hsize : (M : ℝ) < Real.exp (G-1)) (p q : ℕ)
    (hp : p ∈ giantPrimeSupport G) (hq : q ∈ giantPrimeSupport G) :
    jointUnitTest (primeTest R) (fun t : Bool => if t then (q : ZMod M) else (p : ZMod M)) =
      R (p,q) := by
  let u : Bool → (ZMod M)ˣ := fun t => if t then
    giantPrimeUnit G M (NeZero.pos M) hsize q hq else
    giantPrimeUnit G M (NeZero.pos M) hsize p hp
  have hu : (fun t => (u t : ZMod M)) =
      (fun t : Bool => if t then (q : ZMod M) else (p : ZMod M)) := by
    funext t
    cases t <;> simp [u]
  rw [← hu,jointUnitTest_units]
  simp only [primeTest,u,Bool.false_eq_true,ite_false,ite_true,giantPrimeUnit_coe]

theorem jointUnitTest_mixedTest (G : ℝ) (M : ℕ) [NeZero M]
    (R : ZMod M × ZMod M → ℂ) (hsize : (M : ℝ) < Real.exp (G-1)) (n : ℤ) (p : ℕ)
    (hp : p ∈ giantPrimeSupport G) :
    jointUnitTest (mixedTest R (n : ZMod M)) (fun _ : Unit => (p : ZMod M)) =
      R (n,p) := by
  let u : Unit → (ZMod M)ˣ := fun _ => giantPrimeUnit G M (NeZero.pos M) hsize p hp
  have hu : (fun i => (u i : ZMod M)) = (fun _ : Unit => (p : ZMod M)) := by
    funext i
    exact giantPrimeUnit_coe G M (NeZero.pos M) hsize p hp
  rw [← hu,jointUnitTest_units]
  simp only [mixedTest,u,giantPrimeUnit_coe]

end Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement

end

end OAI
