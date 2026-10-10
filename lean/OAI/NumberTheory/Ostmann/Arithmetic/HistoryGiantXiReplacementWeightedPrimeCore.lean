import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPrincipalMassBoundsOriginal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualErrorDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementUncorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementWeightedAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementWeightedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementWeightedPrimeAnalytic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted
open HistoryGiantXiReplacementActual HistoryGiantXiReplacementUncorrected HistoryGiantWeightedPriorReplacement
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
      l ≤ k₀ → TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
      SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
        k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
        (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) →
    ∀ (deleted : Finset ℕ) (hZ : 0 < logCellMass C.giantCenter deleted)
      (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
      (W : ZMod M × ZMod M → ℂ) (BW : ℝ), 0 ≤ BW → (∀ z, ‖W z‖ ≤ BW) →
      GeometryBounds δ L₀ C.giantCenter M L →
      PrimeBounds k₀ δ K L₀ C.giantCenter L M deleted →
      ‖primeDifference C s h k hs ks deleted hZ M hd W‖ ≤
        BW*primeErrorUpper C h k outside deleted M hd K δ := by
  obtain ⟨δ,K,L₀,hδ,hK,hL₀,hreplace⟩ := exists_weighted_corrected_sourcePrimeMean_replacement_constants
  refine ⟨δ,K,L₀,hδ,hK,hL₀,?_⟩
  intro d Bs BD Bz L k₀ l E C s outside hX hout houtlen h k hs ks hl hh hk
    hsrc₁ hsrc₂ deleted hZ M _ hd W BW hBW hW hg hb
  have hcorr := empty_counterpartBounds k₀ l h k (giantCoordinates h k) (pairBackground h k)
    (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)
  have hraw := hreplace d (bulkSize k₀ L/2) s k₀ C.scale C.bulkBin C.spectatorBin C.giantCenter
    (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2)) outside hX hout houtlen
    l (frequencyBound Bs BD Bz k₀ L) h k hs ks hl hh hk
    Empty 0 0
    (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
    [] [] Empty.elim Empty.elim hsrc₁ hsrc₂ hcorr (selected_Xi_source_center C)
    deleted hZ M hd W BW hBW hW hg.modulus_lt_cell (fun _ => meshWidth giant L) hg.lower_threshold
    (fun _ => ⟨hb.mesh_pos,hb.mesh_le_one⟩) hg.modulus_admissible
    (giantPrimeError K δ C.giantCenter deleted) 2 (meshWidth giant L) hb.error_nonneg
    (by norm_num) hb.mesh_pos.le (fun _ => le_rfl)
    (fun j i => (hb.boxes Bool j i).2.2.2.1)
    (fun j i => (add_le_add le_rfl (hb.boxes Bool j i).2.2.2.1).trans
      (hb.boxes Bool j i).2.2.2.2)
  dsimp only at hraw
  rw [corrected_empty_eq] at hraw
  simp only [primeTest] at hraw
  rw [principalIntegral_pair M _ _ _ _ (fun z =>
    weightedResidueTest (residueTransform d) (frequencyBound Bs BD Bz k₀ L) outside h k M hd W
      ((z.1:ZMod M),(z.2:ZMod M)))] at hraw
  have hmass := HistoryGiantPrincipalMassBounds.original_giant_principal_masses M
    (Nat.pos_of_ne_zero (NeZero.ne M)) (bulkSize k₀ L) C.giantCenter deleted
    (by have := hg.lower_threshold; linarith) hZ hb.inverse_cost
  have hD := empty_derivative_le_reference C h k [false,true]
  have hmesh := hb.mesh_pos.le
  have herror := hb.error_nonneg
  have he (ε : ℝ) : 2*ε*(2:ℝ)^2 = 8*ε := by ring
  simp only [he] at hraw
  have hsum := sum_norm_primeTest_weighted_le (residueTransform d)
    (frequencyBound Bs BD Bz k₀ L) outside h k M hd W BW hW
  simp only [primeTest] at hsum
  apply hraw.trans
  change _ ≤ BW*primeErrorUpper C h k outside deleted M hd K δ
  unfold primeErrorUpper referenceAmplitude
  dsimp only
  have hmn := hmass.1.1
  have hDnonneg := correctedPairDerivativeBound_nonneg
    (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l) 0 0
    (Fintype.card (Empty ⊕ Fin ([false,true] : List Bool).length)) h k
    (frequencyBound Bs BD Bz k₀ L) (bulkSize k₀ L/2) k₀ C.bulkBin
    (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2))
  apply weighted_error_mono _ _ _ _ _ _ _ hBW (by positivity) ?_ (by positivity) hsum
  gcongr <;> exact hD

end Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

end

end OAI
