import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementBasic
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkReferencePeriodicMean
open Construction HistoryGiantReferenceMean HistoryGiantWeightedPriorReplacement

def primeTerm (M : ℕ) (R : ZMod M×ZMod M→ℂ) (f : (Bool→ℝ)→ℂ)
    (P Q : ℤ) : ℂ :=
  if Nat.Coprime P.natAbs Q.natAbs then
    R (P,Q)*f (fun t=>if t then (Q:ℝ) else (P:ℝ)) else 0

def mixedTerm (M : ℕ) (R : ZMod M×ZMod M→ℂ) (f : (Option Unit→ℝ)→ℂ)
    (P Q : ℤ) : ℂ :=
  if Nat.Coprime P.natAbs Q.natAbs then
    R (P,Q)*f (Option.elim' (P:ℝ) (fun _ : Unit=>(Q:ℝ))) else 0

theorem primeMean_periodic (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (M : ℕ) (R : ZMod M×ZMod M→ℂ) (f : (Bool→ℝ)→ℂ) :
    primeMean (logCellPrimeSource G E hZ) (primeTerm M R f)=
      guardedPeriodicSourcePrimeMean G E hZ M R f := by
  simp only [primeMean,primeTerm,guardedPeriodicSourcePrimeMean,Int.natAbs_natCast,
    Int.cast_natCast]

theorem mixedMean_periodic (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (M : ℕ) (R : ZMod M×ZMod M→ℂ) (f : (Option Unit→ℝ)→ℂ) :
    mixedMean G (logCellPrimeSource G E hZ) (mixedTerm M R f)=
      guardedPeriodicSourceMixedMean G E hZ M R f := by
  simp only [mixedMean,mixedTerm,guardedPeriodicSourceMixedMean,Int.natAbs_natCast,
    Int.cast_natCast]

theorem primeMean_mul_left (giant : PrimeSource) (c : ℂ) (F : ℤ→ℤ→ℂ) :
    primeMean giant (fun P Q=>c*F P Q)=c*primeMean giant F := by
  simp only [primeMean,FinitePrior.cmean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem mixedMean_mul_left (G : ℝ) (giant : PrimeSource) (c : ℂ) (F : ℤ→ℤ→ℂ) :
    mixedMean G giant (fun P Q=>c*F P Q)=c*mixedMean G giant F := by
  simp only [mixedMean,FinitePrior.cmean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem primeMean_masked_periodic (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (M : ℕ) (R : ZMod M×ZMod M→ℂ) (f : (Bool→ℝ)→ℂ) (mask comp : ℂ) :
    primeMean (logCellPrimeSource G E hZ) (fun P Q=>mask*comp*primeTerm M R f P Q)=
      mask*comp*guardedPeriodicSourcePrimeMean G E hZ M R f := by
  rw [primeMean_mul_left,primeMean_periodic]

theorem mixedMean_masked_periodic (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (M : ℕ) (R : ZMod M×ZMod M→ℂ) (f : (Option Unit→ℝ)→ℂ) (mask comp : ℂ) :
    mixedMean G (logCellPrimeSource G E hZ) (fun P Q=>mask*comp*mixedTerm M R f P Q)=
      mask*comp*guardedPeriodicSourceMixedMean G E hZ M R f := by
  rw [mixedMean_mul_left,mixedMean_periodic]

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMean

end

end OAI
