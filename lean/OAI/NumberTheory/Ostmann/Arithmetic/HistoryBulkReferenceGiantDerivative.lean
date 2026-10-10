import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativePlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeSmooth
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsNorm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairSmoothXi HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryActiveCoordinates HistorySymbolicEncoding HistoryProductWindows HistoryBulkCorrectedXiBounds
open HistoryBulkGiantCorrectedBounds HistorySelectedPairDerivativeBounds PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem corrected_giant_bounds
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀)
    (hm : 1 ≤ bulkSize k₀ L) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (hl : l < k₀)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (matchRoots : RootMatching h k)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    ContDiff ℝ ∞ (fun z : κ → ℝ => jointCorrectedScalar C s h k hs ks eG eB
      (fun j => Real.exp (z j)) u) ∧
    ∀ z ∈ logRectangle (fun _ : κ => C.giantCenter-1) (fun _ => C.giantCenter+1),
      (∀ i : κ, ‖deriv (fun t => jointCorrectedScalar C s h k hs ks eG eB
        (Expr.logCurve (fun j => Real.exp (z j)) i t) u) 0‖ ≤
          Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1))) ∧
      ‖jointCorrectedScalar C s h k hs ks eG eB (fun j => Real.exp (z j)) u‖ ≤
        Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  refine ⟨corrected_giant_log_contDiff C s houtside h k hs ks hsrc₁ hsrc₂ eG eB u hu,?_⟩
  intro z hz
  constructor
  · exact fun i => corrected_giant_deriv_le C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eG eB u hu z hz i
  · exact (HistorySelectedJointIntegralBounds.jointCorrectedScalar_norm_le C s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eG eB z hz u hu).trans
      (selected_amplitude_bound Bs BD Bz L hBs hk₀ hl.le)

theorem plain_giant_bounds
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (hBs : 0 ≤ Bs) (hk₀ : 0 < k₀)
    (hm : 1 ≤ bulkSize k₀ L) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside) (hl : l ≤ k₀)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (matchRoots : RootMatching h k)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    ContDiff ℝ ∞ (fun z : κ → ℝ => jointScalar C s h k hs ks eG eB
      (fun j => Real.exp (z j)) u) ∧
    ∀ z ∈ logRectangle (fun _ : κ => C.giantCenter-1) (fun _ => C.giantCenter+1),
      (∀ i : κ, ‖deriv (fun t => jointScalar C s h k hs ks eG eB
        (Expr.logCurve (fun j => Real.exp (z j)) i t) u) 0‖ ≤
          Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1))) ∧
      ‖jointScalar C s h k hs ks eG eB (fun j => Real.exp (z j)) u‖ ≤
        Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  refine ⟨plain_giant_log_contDiff C s houtside h k hs ks hsrc₁ hsrc₂ eG eB u hu,?_⟩
  intro z hz
  constructor
  · exact fun i => plain_giant_deriv_le C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eG eB u hu z hz i
  · exact (HistorySelectedJointIntegralBounds.jointScalar_norm_le C s houtside hout h k hs ks 
      matchRoots hsrc₁ hsrc₂ eG eB z hz u hu).trans
      (selected_amplitude_bound Bs BD Bz L hBs hk₀ hl)

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
