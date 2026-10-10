import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsAmplitude

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairSmoothXi HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryActiveCoordinates HistorySymbolicEncoding HistoryProductWindows HistoryBulkCorrectedXiBounds
open HistoryBulkGiantCorrectedBounds HistorySelectedPairDerivativeBounds PrimeCellFreezing
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

theorem plain_giant_deriv_le
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
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (z : κ → ℝ)
    (hz : z ∈ logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (i : κ) :
    ‖deriv (fun t => jointScalar C s h k hs ks eG eB
      (Expr.logCurve (fun j => Real.exp (z j)) i t) u) 0‖ ≤
      Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  let b := bulkSize k₀ L/2
  let center := C.cells.center b
  let background := insert (bulkCoordinates h k) (pairBackground h k) (fun j => u (eB.symm j))
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  have hbg₀ : ∀ j, 0 < pairBackground h k j := by
    intro j
    obtain ⟨a,rfl⟩ := unionMap_surjective h k j
    rcases a with a | a
    · exact hsrc₁.background_source.positive a
    · exact hsrc₂.background_source.positive a
  have hbg : ∀ j, 0 < background j :=
    insert_positive _ _ _ hbg₀ (fun j => hu (eB.symm j))
  have hsourceG := giant_sourceDomains C h k hsrc₁ hsrc₂ eG z hz
  have hsource := bulk_sourceDomains h k hs matchRoots _ hsourceG.1 hsourceG.2
    (fun j => u (eB.symm j)) (fun j => hu (eB.symm j))
  change SourceDomain b k₀ C.giantCenter center h
      (fun a => jointInsert h k eG eB (pairBackground h k) (fun j => Real.exp (z j)) u (leftMap h k a)) ∧
    SourceDomain b k₀ C.giantCenter center k
      (fun a => jointInsert h k eG eB (pairBackground h k) (fun j => Real.exp (z j)) u (rightMap h k a)) at hsource
  simp only [jointInsert_commute] at hsource
  simp_rw [jointScalar_giant_first]
  exact (reindexedRealXi_deriv_le b s k₀ C.scale C.bulkBin C.spectatorBin C.giantCenter
    (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) center hX houtside hout h k hs ks hl hh hk
    (giantCoordinates h k) background hbg eG (fun j => Real.exp (z j)) i
    (fun j => Real.exp_pos _) hsource.1 hsource.2 (selected_Xi_source_center C)).trans
    (selected_pair_bound C hBs hk₀ hm hl h k hh hk)

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
