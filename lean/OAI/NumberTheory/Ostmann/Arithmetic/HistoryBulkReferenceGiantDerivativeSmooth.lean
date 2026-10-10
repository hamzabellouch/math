import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsRegularity

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryBulkGiantCorrectedBounds
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem corrected_giant_log_contDiff
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀i,0 < u i) :
    ContDiff ℝ ∞ (fun z : κ → ℝ =>
      jointCorrectedScalar C s h k hs ks eG eB (fun j => Real.exp (z j)) u) := by
  have hc : ContDiff ℝ ∞ (fun z : κ → ℝ => (z,fun i : ι => Real.log (u i))) := by
    fun_prop
  have hh := (jointCorrectedScalar_log_contDiff C s houtside h k hs ks hsrc₁ hsrc₂ eG eB).comp hc
  have he : (fun i : ι => Real.exp (Real.log (u i))) = u :=
    funext (fun i => Real.exp_log (hu i))
  simpa only [Function.comp_def,he] using hh

theorem plain_giant_log_contDiff
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (u : ι → ℝ) (hu : ∀i,0 < u i) :
    ContDiff ℝ ∞ (fun z : κ → ℝ =>
      jointScalar C s h k hs ks eG eB (fun j => Real.exp (z j)) u) := by
  have hc : ContDiff ℝ ∞ (fun z : κ → ℝ => (z,fun i : ι => Real.log (u i))) := by
    fun_prop
  have hh := (jointScalar_log_contDiff C s houtside h k hs ks hsrc₁ hsrc₂ eG eB).comp hc
  have he : (fun i : ι => Real.exp (Real.log (u i))) = u :=
    funext (fun i => Real.exp_log (hu i))
  simpa only [Function.comp_def,he] using hh

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
