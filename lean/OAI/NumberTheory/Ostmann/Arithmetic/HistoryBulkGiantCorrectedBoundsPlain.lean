import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsAmplitude

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern HistoryPairSmoothXi
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistorySymbolicEncoding HistoryProductWindows HistoryBulkIntegralReplacement
open HistorySelectedPairDerivativeBounds HistorySelectedPairDerivativeCounts
open HistoryBulkCorrectedXiBounds PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem plain_bulkBounds
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
    (z : κ → ℝ)
    (hz : z ∈ logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1)) :
    BulkBounds k₀ L (selectedExponent Bs BD Bz k₀)
      (jointScalar C s h k hs ks eG eB (fun i => Real.exp (z i))) := by
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  let background := insert (giantCoordinates h k) (pairBackground h k)
    (fun j => Real.exp (z (eG.symm j)))
  have hsource := giant_sourceDomains C h k hsrc₁ hsrc₂ eG z hz
  have hbg : ∀ i, 0 < background i := by
    intro i
    obtain ⟨j,rfl⟩ := unionMap_surjective h k i
    rcases j with j | j
    · exact hsource.1.positive j
    · exact hsource.2.positive j
  have hbulk (x : ι → ℝ) (hx : ∀ i, 0 < x i) :=
    bulk_sourceDomains h k hs matchRoots background hsource.1 hsource.2
      (fun j => x (eB.symm j)) (fun j => hx (eB.symm j))
  have hD := selected_pair_bound C hBs hk₀ hm hl h k hh hk
  have hA := selected_amplitude_bound Bs BD Bz L hBs hk₀ hl
  have hA' : Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k₀ L+sourceXiConstant l k₀ (2+2*(k₀:ℝ))) ≤
      Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
    apply le_trans _ hA
    exact le_mul_of_one_le_left (Real.exp_nonneg _) (Real.one_le_exp (by
      unfold nominalInheritedWidth nominalRemovedWidth
      positivity))
  refine ⟨?_,?_,?_⟩
  · intro y hy
    exact (reindexedRealXi_log_contDiff (bulkSize k₀ L/2) s C.scale C.bulkBin C.spectatorBin
      C.giantCenter hX houtside h k hs ks (bulkCoordinates h k) background hbg eB).differentiable (by simp) y
  · intro y hy i
    have hb := hbulk (fun j => Real.exp (y j)) (fun j => Real.exp_pos _)
    exact (reindexedRealXi_deriv_le (bulkSize k₀ L/2) s k₀ C.scale C.bulkBin C.spectatorBin
      C.giantCenter (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2))
      hX houtside hout h k hs ks hl hh hk (bulkCoordinates h k) background hbg eB
      (fun j => Real.exp (y j)) i (fun j => Real.exp_pos _) hb.1 hb.2
      (selected_Xi_source_center C)).trans hD
  · intro y hy
    have hb := hbulk (fun j => Real.exp (y j)) (fun j => Real.exp_pos _)
    exact (pairedRealXi_norm_le (bulkSize k₀ L/2) s k₀ C.scale C.bulkBin C.spectatorBin
      C.giantCenter (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) (C.cells.center (bulkSize k₀ L/2))
      hX houtside hout h k hs ks _ hb.1 hb.2 (selected_Xi_source_center C)).trans hA'

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
