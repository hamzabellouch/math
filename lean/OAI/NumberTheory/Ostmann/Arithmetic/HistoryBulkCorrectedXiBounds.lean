import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsActive
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsRemoved
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsZero

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ContDiff
namespace Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryProductWindows HistoryPairSmoothXi HistoryPairPattern
open HistoryPairBulkCoordinates HistoryActiveCoordinates InitialCoordinatesTemplate

theorem selected_bulk_corrected_bounds {d : Decomposition} {Bs BD Bz : ℝ} {k₀ l : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (s : ℕ) (X Δ Err : ℝ) (hX : 0 < X) {V : ℕ → ℕ} {outside : List ℕ}
    (houtside : ∀q∈outside,0 < q) (hout : outside.length = 2*s)
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hl : l < k₀)
    (hl₁ : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) h)
    (hl₂ : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (matchRoots : RootMatching h k) (background : PairKey h k → ℝ)
    (hsrc₁ : SourceDomain (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      h (fun i => background (leftMap h k i)))
    (hsrc₂ : SourceDomain (bulkSize k₀ L/2) k₀ C.giantCenter (C.cells.center (bulkSize k₀ L/2))
      k (fun i => background (rightMap h k i)))
    (hcenter : Real.log X+Δ-Err ≤ 2*(C.giantCenter:ℝ)+2*C.bulkBin+2*C.spectatorBin+
      (∑a,∑i,topCenters (bulkSize k₀ L/2) (C.cells.center (bulkSize k₀ L/2)) a i)+
      (∑a,∑j:Fin k₀,∑i,compensationCenters (bulkSize k₀ L/2) (C.cells.center (bulkSize k₀ L/2)) a j i))
    {τ : Type} (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ bulkCoordinates h k) :
    let T := (C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l
    let U := C.compensationLogScale l
    let WH := nominalInheritedWidth k₀ l+1
    let Wu := nominalRemovedWidth k₀ l
    let f := reindexedCorrectedRealXi (bulkSize k₀ L/2) s X C.bulkBin C.spectatorBin C.giantCenter h k hs ks
      T U (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1)) S cellCenter cellKey
      (bulkCoordinates h k) background e
    ContDiff ℝ ∞ (fun y : ι → ℝ => f (fun i => Real.exp (y i))) ∧
    (∀x : ι → ℝ, (∀i,0 < x i) → ∀i,
      ‖deriv (fun t => f (Expr.logCurve x i t)) 0‖ ≤
        correctedPairDerivativeBound WH Wu (pairedDiagonalHKeys h k (l+1)).length
          (pairedDiagonalUKeys h k (l+1)).length S.card h k V (bulkSize k₀ L/2) k₀ C.bulkBin Δ Err
          (C.cells.center (bulkSize k₀ L/2))) ∧
    (∀x : ι → ℝ, (∀i,0 < x i) →
      ‖f x‖ ≤ Real.exp (WH+Wu)*Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ Err)) := by
  dsimp only
  let b := bulkSize k₀ L/2
  let center := C.cells.center b
  let T := (C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l
  let U := C.compensationLogScale l
  let WH := nominalInheritedWidth k₀ l
  let Wu := nominalRemovedWidth k₀ l
  let Hkeys := pairedDiagonalHKeys h k (l+1)
  let Ukeys := pairedDiagonalUKeys h k (l+1)
  let point (x : ι → ℝ) := insert (bulkCoordinates h k) background (fun j => x (e.symm j))
  let f := reindexedCorrectedRealXi b s X C.bulkBin C.spectatorBin C.giantCenter h k hs ks
    T U Hkeys Ukeys S cellCenter cellKey (bulkCoordinates h k) background e
  have hbg : ∀i,0 < background i := by
    intro i
    obtain ⟨j,rfl⟩ := unionMap_surjective h k i
    rcases j with j | j
    · exact hsrc₁.positive j
    · exact hsrc₂.positive j
  have hsource (x : ι → ℝ) (hx : ∀i,0 < x i) :=
    bulk_sourceDomains h k hs matchRoots background hsrc₁ hsrc₂ _ (fun j => hx (e.symm j))
  have hpos (x : ι → ℝ) (hx : ∀i,0 < x i) : ∀j,0 < point x j :=
    insert_positive _ background _ hbg (fun j => hx (e.symm j))
  have hwindow (x : ι → ℝ) (hx : ∀i,0 < x i) (hne : f x ≠ 0) :
      T-WH ≤ Real.log ((Hkeys.map (point x)).prod) := by
    have hn : pairedRealXi b s X C.bulkBin C.spectatorBin C.giantCenter h k hs ks (point x) ≠ 0 := by
      intro hz
      apply hne
      change (_:ℂ)*pairedRealXi b s X C.bulkBin C.spectatorBin C.giantCenter h k hs ks (point x)=0
      rw [hz,mul_zero]
    have hw := selected_paired_H_window C s hl X h k hs ks hl₂ (point x) (hsource x hx).2 hn
    have hh := (abs_le.mp hw).1
    change -WH ≤ Real.log ((Hkeys.map (point x)).prod)-T at hh
    linarith
  have hupper (x : ι → ℝ) (hx : ∀i,0 < x i) :
      Real.log ((Ukeys.map (point x)).prod) ≤ U+Wu := by
    have hw := selected_paired_U_window C hl h k hl₂ (point x) (hsource x hx).2
    have hh := (abs_le.mp hw).2
    change Real.log ((Ukeys.map (point x)).prod)-U ≤ Wu at hh
    linarith
  refine ⟨reindexedCorrectedRealXi_log_contDiff b s X C.bulkBin C.spectatorBin C.giantCenter hX
    houtside h k hs ks T U Hkeys Ukeys S cellCenter cellKey (bulkCoordinates h k) background hbg e,?_,?_⟩
  · intro x hx i
    by_cases hH : T-(WH+1) ≤ Real.log ((Hkeys.map (point x)).prod)
    · exact reindexedCorrectedRealXi_deriv_le b s k₀ X C.bulkBin C.spectatorBin C.giantCenter
        Δ Err center hX houtside hout h k hs ks hl.le hl₁ hl₂ T U (WH+1) Wu Hkeys Ukeys
        S cellCenter cellKey _ background hbg e x i hx hH (hupper x hx)
        (hsource x hx).1 (hsource x hx).2 hcenter
    · have hz : deriv (fun t => f (Expr.logCurve x i t)) 0 = 0 := by
        apply deriv_eq_zero_below_support _
          (fun t => Real.log ((Hkeys.map (point (Expr.logCurve x i t))).prod)) (T-WH)
          (log_product_insert_logCurve_continuousAt _ background hbg e x hx i Hkeys)
        · intro t ht
          exact hwindow _ (logCurve_positive x hx i t) ht
        · simpa only [Expr.logCurve_zero] using
            (show Real.log ((Hkeys.map (point x)).prod) < T-WH by linarith)
      change ‖deriv (fun t => f (Expr.logCurve x i t)) 0‖ ≤ _
      rw [hz,norm_zero]
      exact correctedPairDerivativeBound_nonneg (WH+1) Wu Hkeys.length Ukeys.length S.card
        h k V b k₀ C.bulkBin Δ Err center
  · intro x hx
    by_cases hz : f x = 0
    · change ‖f x‖ ≤ _
      rw [hz,norm_zero]
      positivity
    · have hH : T-(WH+1) ≤ Real.log ((Hkeys.map (point x)).prod) := by
        linarith [hwindow x hx hz]
      exact correctedPairedRealXi_norm_le b s k₀ X C.bulkBin C.spectatorBin C.giantCenter
        Δ Err center hX houtside hout h k hs ks T U (WH+1) Wu Hkeys Ukeys S cellCenter cellKey
        (point x) (hpos x hx) hH (hupper x hx) (hsource x hx).1 (hsource x hx).2 hcenter

end Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds

end

end OAI
