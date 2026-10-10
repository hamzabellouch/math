import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedJointIntegralBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkCorrectedXiBounds
open HistoryBulkGiantCorrectedBounds PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

def mainAmplitude (Bs : ℝ) (k₀ : ℕ) (L : ℝ) (l : ℕ) : ℝ :=
  Real.exp ((nominalInheritedWidth k₀ l+2)+nominalRemovedWidth k₀ l) *
    Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k₀ L+
      sourceXiConstant l k₀ (2+2*(k₀:ℝ)))

lemma mainAmplitude_pos (Bs : ℝ) (k₀ : ℕ) (L : ℝ) (l : ℕ) :
    0 < mainAmplitude Bs k₀ L l := by
  unfold mainAmplitude
  positivity

theorem jointCorrectedScalar_norm_le
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) {outside : List ℕ}
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
    (z : κ → ℝ)
    (hz : z ∈ logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    ‖jointCorrectedScalar C s h k hs ks eG eB (fun i => Real.exp (z i)) x‖ ≤
      mainAmplitude Bs k₀ L l := by
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  have hsource := giant_sourceDomains C h k hsrc₁ hsrc₂ eG z hz
  have hr := selected_bulk_corrected_bounds C s C.scale (initialGap Bs k₀ L) (2+2*(k₀:ℝ))
    hX houtside hout h k hs ks hl hh hk matchRoots _ hsource.1 hsource.2
    (selected_Xi_source_center C)
    (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
    (pairedDiagonalCellCenter k (l+1) C.giantCenter (C.cells.center (bulkSize k₀ L/2)))
    (pairedDiagonalCellKey h k (l+1)) eB
  apply (hr.2.2 x hx).trans
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _)

theorem jointScalar_norm_le
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) {outside : List ℕ}
    (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (matchRoots : RootMatching h k)
    (hsrc₁ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (leftMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (hsrc₂ : SourceBounds (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (rightMap h k) (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (eG : κ ≃ giantCoordinates h k) (eB : ι ≃ bulkCoordinates h k)
    (z : κ → ℝ)
    (hz : z ∈ logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    ‖jointScalar C s h k hs ks eG eB (fun i => Real.exp (z i)) x‖ ≤
      mainAmplitude Bs k₀ L l := by
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  let background := insert (giantCoordinates h k) (pairBackground h k)
    (fun j => Real.exp (z (eG.symm j)))
  have hsource := giant_sourceDomains C h k hsrc₁ hsrc₂ eG z hz
  have hb := bulk_sourceDomains h k hs matchRoots background hsource.1 hsource.2
    (fun j => x (eB.symm j)) (fun j => hx (eB.symm j))
  apply (pairedRealXi_norm_le (bulkSize k₀ L/2) s k₀ C.scale C.bulkBin C.spectatorBin
    C.giantCenter (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2))
    hX houtside hout h k hs ks _ hb.1 hb.2 (selected_Xi_source_center C)).trans
  exact le_mul_of_one_le_left (Real.exp_nonneg _) (Real.one_le_exp (by
    unfold nominalInheritedWidth nominalRemovedWidth
    positivity))

end Ostmann.Arithmetic.HistorySelectedJointIntegralBounds

end

end OAI
