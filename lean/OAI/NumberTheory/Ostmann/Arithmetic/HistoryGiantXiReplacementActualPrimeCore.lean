import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualErrorDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryPairGiantCoordinates HistoryProductWindows
open HistoryGiantXiPriorReplacement HistoryGiantGridCellBounds HistoryGiantReplacementGeometry
open HistorySignedResidues HistoryPrincipalIntegralAverage PrimeCellActualErrorBudget
open ScaleBudget PrimeCellMeshBudget LogCellPartition HistoryActiveCoordinates

theorem exists_prime_replacement_core :
    ∃ δ K L₀ : ℝ, 0 < δ ∧ 0 < K ∧ 1 ≤ L₀ ∧
    ∀ {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}
      (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) (outside : List ℕ),
      0 < (C.scale:ℝ) → (∀ q ∈ outside, q.Prime) → outside.length = 2*s →
    ∀ (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
      (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside),
      l < k₀ → TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k → RootGiantsAgree h k →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
      pairedRealXi (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin C.giantCenter
        h k hs ks (pairBackground h k) ≠ 0 →
    ∀ (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
      (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M),
      GeometryBounds δ L₀ C.giantCenter M L →
      PrimeBounds k₀ δ K L₀ C.giantCenter L M deleted →
      ‖primeDifference C s h k hs ks deleted hZ M hd‖ ≤
        primeErrorUpper C h k outside deleted M hd K δ := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_corrected_sourcePrimeMean_replacement_constants
  refine ⟨δ,K,L₀,hδ,hK,hL₀,?_⟩
  intro d Bs BD Bz L k₀ l E C s outside hX hout houtlen h k hs ks hl hh hk hgiants
    hsrc₁ hsrc₂ hne deleted hZ M _ hd hg hb
  have hcorr := reference_counterpartBounds C s h k hs ks hl hk hgiants hsrc₂ hne
  have hraw := hreplace d (bulkSize k₀ L/2) s k₀ C.scale C.bulkBin C.spectatorBin C.giantCenter
    (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2)) outside hX hout houtlen
    l (frequencyBound Bs BD Bz k₀ L) h k hs ks hl.le hh hk
    (Fin (diagonalCellKeys k (l+1)).length)
    ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l) (C.compensationLogScale l)
    (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
    (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) hsrc₁ hsrc₂ hcorr (selected_Xi_source_center C)
    deleted hZ M hd hg.modulus_lt_cell (fun _ => meshWidth giant L) hg.lower_threshold
    (fun _ => ⟨hb.mesh_pos,hb.mesh_le_one⟩) hg.modulus_admissible
    (giantPrimeError K δ C.giantCenter deleted) 2 (meshWidth giant L) hb.error_nonneg
    (by norm_num) hb.mesh_pos.le (fun _ => le_rfl)
    (fun j i => (hb.boxes Bool j i).2.2.2.1)
    (fun j i => (add_le_add le_rfl (hb.boxes Bool j i).2.2.2.1).trans
      (hb.boxes Bool j i).2.2.2.2)
  dsimp only at hraw
  rw [primeResidueTest_main] at hraw
  have he (ε : ℝ) : 2*ε*(2:ℝ)^2 = 8*ε := by ring
  simpa only [primeDifference,primeScalar,primeErrorUpper,referenceDerivative,referenceAmplitude,he]
    using hraw

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
