import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeCutoffExponent

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open HistoryGiantPriorGrid
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairSmoothXi HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryActiveCoordinates HistorySymbolicEncoding HistoryProductWindows HistoryBulkCorrectedXiBounds
open HistoryBulkGiantCorrectedBounds HistorySelectedPairDerivativeBounds PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem corrected_prime_giant_bounds
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eG : Bool ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    let F := fun v => jointCorrectedScalar C s h k hs ks eG eB v u
    ContDiff ℝ ∞ (fun z : Bool → ℝ => primeCutoff C.giantCenter F
      (fun j => Real.exp (z j))) ∧
    ∀ z ∈ logRectangle (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1),
      (∀ i : Bool, ‖deriv (fun t => primeCutoff C.giantCenter F
        (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1))) ∧
      ‖primeCutoff C.giantCenter F (fun j => Real.exp (z j))‖ ≤
        Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  exact primeCutoff_exp_giant_bounds C.giantCenter (selectedExponent Bs BD Bz k₀) (bulkSize k₀ L)
    _ (corrected_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eG eB u hu)

theorem corrected_mixed_giant_bounds
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eG : Option Unit ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    let F := fun v => jointCorrectedScalar C s h k hs ks eG eB v u
    ContDiff ℝ ∞ (fun z : Option Unit → ℝ => mixedGiantPrimeTest C.giantCenter F
      (fun j => Real.exp (z j))) ∧
    ∀ z ∈ logRectangle (fun _ : Option Unit => C.giantCenter-1) (fun _ => C.giantCenter+1),
      (∀ i : Option Unit, ‖deriv (fun t => mixedGiantPrimeTest C.giantCenter F
        (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1))) ∧
      ‖mixedGiantPrimeTest C.giantCenter F (fun j => Real.exp (z j))‖ ≤
        Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  exact mixedCutoff_exp_giant_bounds C.giantCenter (selectedExponent Bs BD Bz k₀) (bulkSize k₀ L)
    _ (corrected_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eG eB u hu)

theorem plain_prime_giant_bounds
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eG : Bool ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    let F := fun v => jointScalar C s h k hs ks eG eB v u
    ContDiff ℝ ∞ (fun z : Bool → ℝ => primeCutoff C.giantCenter F
      (fun j => Real.exp (z j))) ∧
    ∀ z ∈ logRectangle (fun _ : Bool => C.giantCenter-1) (fun _ => C.giantCenter+1),
      (∀ i : Bool, ‖deriv (fun t => primeCutoff C.giantCenter F
        (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1))) ∧
      ‖primeCutoff C.giantCenter F (fun j => Real.exp (z j))‖ ≤
        Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  exact primeCutoff_exp_giant_bounds C.giantCenter (selectedExponent Bs BD Bz k₀) (bulkSize k₀ L)
    _ (plain_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eG eB u hu)

theorem plain_mixed_giant_bounds
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eG : Option Unit ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    let F := fun v => jointScalar C s h k hs ks eG eB v u
    ContDiff ℝ ∞ (fun z : Option Unit → ℝ => mixedGiantPrimeTest C.giantCenter F
      (fun j => Real.exp (z j))) ∧
    ∀ z ∈ logRectangle (fun _ : Option Unit => C.giantCenter-1) (fun _ => C.giantCenter+1),
      (∀ i : Option Unit, ‖deriv (fun t => mixedGiantPrimeTest C.giantCenter F
        (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1))) ∧
      ‖mixedGiantPrimeTest C.giantCenter F (fun j => Real.exp (z j))‖ ≤
        Real.exp (cutoffExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  exact mixedCutoff_exp_giant_bounds C.giantCenter (selectedExponent Bs BD Bz k₀) (bulkSize k₀ L)
    _ (plain_giant_bounds C hBs hk₀ hm s houtside hout h k hs ks hl hh hk
      matchRoots hsrc₁ hsrc₂ eG eB u hu)

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
