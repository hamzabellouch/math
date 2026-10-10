import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeWindow
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

theorem corrected_giant_deriv_le
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
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (z : κ → ℝ)
    (hz : z ∈ logRectangle (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1))
    (i : κ) :
    ‖deriv (fun t => jointCorrectedScalar C s h k hs ks eG eB
      (Expr.logCurve (fun j => Real.exp (z j)) i t) u) 0‖ ≤
      Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
  let b := bulkSize k₀ L/2
  let center := C.cells.center b
  let T := (C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l
  let U := C.compensationLogScale l
  let WH := nominalInheritedWidth k₀ l
  let Wu := nominalRemovedWidth k₀ l
  let Hkeys := pairedDiagonalHKeys h k (l+1)
  let Ukeys := pairedDiagonalUKeys h k (l+1)
  let S := (Finset.univ : Finset (Fin (diagonalCellKeys k (l+1)).length))
  let cellCenter := pairedDiagonalCellCenter k (l+1) C.giantCenter center
  let cellKey := pairedDiagonalCellKey h k (l+1)
  let background := insert (bulkCoordinates h k) (pairBackground h k) (fun j => u (eB.symm j))
  let point (y : κ → ℝ) := insert (giantCoordinates h k) background (fun j => y (eG.symm j))
  let f := reindexedCorrectedRealXi b s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    T U Hkeys Ukeys S cellCenter cellKey (giantCoordinates h k) background eG
  have hX : 0 < (C.scale:ℝ) := by exact_mod_cast InitialEta.initial_scale_pos C
  have hbg₀ : ∀ j, 0 < pairBackground h k j := by
    intro j
    obtain ⟨a,rfl⟩ := unionMap_surjective h k j
    rcases a with a | a
    · exact hsrc₁.background_source.positive a
    · exact hsrc₂.background_source.positive a
  have hbg : ∀ j, 0 < background j :=
    insert_positive _ _ _ hbg₀ (fun j => hu (eB.symm j))
  have hbase := bulk_sourceDomains h k hs matchRoots (pairBackground h k)
    hsrc₁.background_source hsrc₂.background_source (fun j => u (eB.symm j))
    (fun j => hu (eB.symm j))
  have hsourceG := giant_sourceDomains C h k hsrc₁ hsrc₂ eG z hz
  have hsource := bulk_sourceDomains h k hs matchRoots _ hsourceG.1 hsourceG.2
    (fun j => u (eB.symm j)) (fun j => hu (eB.symm j))
  change SourceDomain b k₀ C.giantCenter center h
      (fun a => jointInsert h k eG eB (pairBackground h k) (fun j => Real.exp (z j)) u (leftMap h k a)) ∧
    SourceDomain b k₀ C.giantCenter center k
      (fun a => jointInsert h k eG eB (pairBackground h k) (fun j => Real.exp (z j)) u (rightMap h k a)) at hsource
  simp only [jointInsert_commute] at hsource
  have hpointpos (y : κ → ℝ) (hy : ∀ j, 0 < y j) : ∀ j, 0 < point y j :=
    insert_positive _ _ _ hbg (fun j => hy (eG.symm j))
  have hupper : Real.log ((Ukeys.map (point (fun j => Real.exp (z j)))).prod) ≤ U+Wu := by
    have hw := selected_paired_U_window C hl h k hk _ hsource.2
    have hh := (abs_le.mp hw).2
    change Real.log ((Ukeys.map (point (fun j => Real.exp (z j)))).prod)-U ≤ Wu at hh
    linarith
  have hwindow (t : ℝ) (ht : |t| ≤ 1)
      (hne : f (Expr.logCurve (fun j => Real.exp (z j)) i t) ≠ 0) :
      T-(WH+1) ≤ Real.log ((Hkeys.map (point (Expr.logCurve (fun j => Real.exp (z j)) i t))).prod) := by
    let y := Expr.logCurve (fun j => Real.exp (z j)) i t
    have hy : ∀ j, 0 < y j := logCurve_positive _ (fun j => Real.exp_pos _) i t
    have hn : pairedRealXi b s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks (point y) ≠ 0 := by
      intro hz
      apply hne
      change (_:ℂ)*pairedRealXi b s C.scale C.bulkBin C.spectatorBin C.giantCenter h k hs ks (point y)=0
      rw [hz,mul_zero]
    have hsmall := giant_insert_right_source h k center background hbase.2.source
      (fun j => y (eG.symm j))
    have hgiant : |Real.log (point y (rightMap h k (.inl true)))-(C.giantCenter:ℝ)| ≤ 2 := by
      rw [←shared_giant h k true]
      change |Real.log (insert (giantCoordinates h k) background (fun j => y (eG.symm j))
        (leftMap h k (.inl true)))-(C.giantCenter:ℝ)| ≤ 2
      simp only [HistoryActiveCoordinates.insert,dite_eq_left (giant_mem h k true)]
      exact logCurve_giant_window C.giantCenter z hz i _ t ht
    have hw := HistoryBulkReferenceGiantDerivativeWindow.selected_paired_H_window_relaxed
      C s hl C.scale h k hs ks hk (point y) (hpointpos y hy) hsmall hbase.2.leaves hgiant hn
    have hh := (abs_le.mp hw).1
    change -(WH+1) ≤ Real.log ((Hkeys.map (point y)).prod)-T at hh
    linarith
  have hD : correctedPairDerivativeBound (WH+2) Wu Hkeys.length Ukeys.length S.card h k
      (frequencyBound Bs BD Bz k₀ L) b k₀ C.bulkBin (initialGap Bs k₀ L)
      (2+2*(k₀:ℝ)) center ≤
      Real.exp (selectedExponent Bs BD Bz k₀*((bulkSize k₀ L:ℝ)+1)) := by
    have hcount := HistorySelectedPairDerivativeCounts.diagonal_cells_card_le hk hl.le (l+1)
    simp only [Finset.card_univ,Fintype.card_fin] at hcount
    apply selected_corrected_bound C hBs hk₀ hm hl.le h k hh hk (l+1)
    simp only [S,Finset.card_univ,Fintype.card_fin]
    nlinarith [Nat.zero_le (HistorySelectedPairDerivativeCounts.countCoefficient k₀*(bulkSize k₀ L/2+1))]
  simp_rw [jointCorrectedScalar_giant_first]
  change ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ _
  by_cases hH : T-(WH+2) ≤ Real.log ((Hkeys.map (point (fun j => Real.exp (z j)))).prod)
  · exact (reindexedCorrectedRealXi_deriv_le b s k₀ C.scale C.bulkBin C.spectatorBin C.giantCenter
      (initialGap Bs k₀ L) (2+2*(k₀:ℝ)) center hX houtside hout h k hs ks hl.le hh hk
      T U (WH+2) Wu Hkeys Ukeys S cellCenter cellKey _ background hbg eG
      (fun j => Real.exp (z j)) i (fun j => Real.exp_pos _) hH hupper
      hsource.1 hsource.2 (selected_Xi_source_center C)).trans hD
  · have hzderiv : deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0 = 0 := by
      apply deriv_eq_zero_below_local_support _
        (fun t => Real.log ((Hkeys.map (point (Expr.logCurve (fun j => Real.exp (z j)) i t))).prod))
        (T-(WH+1))
        (log_product_insert_logCurve_continuousAt _ background hbg eG
          (fun j => Real.exp (z j)) (fun j => Real.exp_pos _) i Hkeys)
      · exact hwindow
      · simpa only [Expr.logCurve_zero] using
          (show Real.log ((Hkeys.map (point (fun j => Real.exp (z j)))).prod) < T-(WH+1) by linarith)
    rw [hzderiv,norm_zero]
    exact (Real.exp_pos _).le

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
