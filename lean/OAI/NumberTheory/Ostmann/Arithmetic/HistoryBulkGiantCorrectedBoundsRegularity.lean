import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsContinuity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem jointCorrectedScalar_log_contDiff
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
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k) :
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>
      jointCorrectedScalar C s h k hs ks eG eB (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) := by
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  have hbg : ∀i,0<pairBackground h k i := by
    intro i
    obtain ⟨j,rfl⟩ := unionMap_surjective h k i
    rcases j with j | j
    · exact hsrc₁.background_source.positive j
    · exact hsrc₂.background_source.positive j
  exact correctedPairedRealXi_joint_log_contDiff (bulkSize k₀ L/2) s C.scale C.bulkBin
    C.spectatorBin C.giantCenter hX houtside h k hs ks
    ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l)
    (C.compensationLogScale l) (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
    (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) eG eB (pairBackground h k) hbg

theorem jointScalar_log_contDiff
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
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k) :
    ContDiff ℝ ∞ (fun z : (κ→ℝ)×(ι→ℝ)=>
      jointScalar C s h k hs ks eG eB (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) := by
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  have hbg : ∀i,0<pairBackground h k i := by
    intro i
    obtain ⟨j,rfl⟩ := unionMap_surjective h k i
    rcases j with j | j
    · exact hsrc₁.background_source.positive j
    · exact hsrc₂.background_source.positive j
  exact pairedRealXi_joint_log_contDiff (bulkSize k₀ L/2) s C.scale C.bulkBin
    C.spectatorBin C.giantCenter hX houtside h k hs ks eG eB (pairBackground h k) hbg

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
