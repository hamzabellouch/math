import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsNorm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedJointIntegralBounds
open Construction PrimeCellFreezing HistoryPrincipalIntegralAverage HistoryGiantPriorGrid
open HistoryBulkPriorGrid

def bulkIntegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℝ) (E : Finset ℕ) (f : (ι → ℝ) → ℂ) : ℂ :=
  primeIntegral (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L)
    (fun _ => bulkNormalizer L E) f

def nestedPrimeIntegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L G : ℝ) (E : Finset ℕ) (f : (Bool → ℝ) → (ι → ℝ) → ℂ) : ℂ :=
  primeIntegral (fun _ : Bool => G-1) (fun _ => G+1)
    (fun _ => logCellMass G ∅) (primeCutoff G (fun u => bulkIntegral L E (f u)))

def nestedMixedIntegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L G : ℝ) (E : Finset ℕ) (f : (Option Unit → ℝ) → (ι → ℝ) → ℂ) : ℂ :=
  mixedIntegral (G-1) (G+1) G smoothPartition (fun _ : Unit => G-1) (fun _ => G+1)
    (fun _ => logCellMass G ∅) (mixedGiantPrimeTest G (fun u => bulkIntegral L E (f u)))

def RectangleBound {κ ι : Type*} (L G A : ℝ)
    (f : (κ → ℝ) → (ι → ℝ) → ℂ) : Prop :=
  ∀ z ∈ logRectangle (fun _ : κ => G-1) (fun _ => G+1),
    ∀ y ∈ logRectangle (fun _ : ι => bulkLogLower L) (fun _ => bulkLogUpper L),
      ‖f (fun i => Real.exp (z i)) (fun i => Real.exp (y i))‖ ≤ A

def IntegralBounds (L G : ℝ) (E : Finset ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], ∀ A : ℝ, 0 ≤ A →
    (∀ f : (Bool → ℝ) → (ι → ℝ) → ℂ, RectangleBound L G A f →
      ‖nestedPrimeIntegral L G E f‖ ≤ 64*2^Fintype.card ι*A) ∧
    (∀ f : (Option Unit → ℝ) → (ι → ℝ) → ℂ, RectangleBound L G A f →
      ‖nestedMixedIntegral L G E f‖ ≤ 64*2^Fintype.card ι*A)

end Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

end

end OAI
