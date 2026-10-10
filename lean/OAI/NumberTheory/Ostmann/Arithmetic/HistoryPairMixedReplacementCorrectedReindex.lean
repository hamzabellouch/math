import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedDeriv

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open PrimeCellFreezing
open scoped ContDiff
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def reindexedCorrectedRealXi (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) {τ : Type}
    (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    {ι : Type*} (e : ι ≃ I) (x : ι → ℝ) : ℂ :=
  correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey
    (insert I background (fun j => x (e.symm j)))

theorem reindexedCorrectedRealXi_log_contDiff (b s : ℕ) (X tb td G : ℝ) (hX : 0 < X)
    (houtside : ∀q ∈ outside,0 < q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) {τ : Type}
    (T U : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    (hbackground : ∀i,0 < background i) {ι : Type*} [Fintype ι] (e : ι ≃ I) :
    ContDiff ℝ ∞ (fun y : ι → ℝ => reindexedCorrectedRealXi b s X tb td G h k hs ks
      T U Hkeys Ukeys S cellCenter cellKey I background e (fun i => Real.exp (y i))) :=
  (log_contDiff_insert _ I background hbackground
    (correctedPairedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks T U Hkeys Ukeys
      S cellCenter cellKey)).comp
    (show ContDiff ℝ ∞ (fun y : ι → ℝ => fun j : I => y (e.symm j)) by fun_prop)

theorem reindexedCorrectedRealXi_deriv_le (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0 < X) (houtside : ∀q ∈ outside,0 < q)
    (hout : outside.length = 2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hlk : l ≤ k₀) (hl₁ : TreeSourceLabels (Template.initial (2*b) k₀) h)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k₀) k) {τ : Type}
    (T U WH Wu : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ) (hbackground : ∀i,0 < background i)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ I) (x : ι → ℝ) (i : ι) (hx : ∀i,0 < x i)
    (hH : T-WH ≤ Real.log ((Hkeys.map (insert I background (fun j => x (e.symm j)))).prod))
    (hu : Real.log ((Ukeys.map (insert I background (fun j => x (e.symm j)))).prod) ≤ U+Wu)
    (hx₁ : SourceDomain b k₀ G center h
      (fun i => insert I background (fun j => x (e.symm j)) (leftMap h k i)))
    (hx₂ : SourceDomain b k₀ G center k
      (fun i => insert I background (fun j => x (e.symm j)) (rightMap h k i)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑a,∑i,topCenters b center a i)+
      (∑a,∑j : Fin k₀,∑i,compensationCenters b center a j i)) :
    ‖deriv (fun t => reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey
      I background e (Expr.logCurve x i t)) 0‖ ≤
      correctedPairDerivativeBound WH Wu Hkeys.length Ukeys.length S.card h k V b k₀ tb Δ E center := by
  unfold reindexedCorrectedRealXi
  simp_rw [reindex_logCurve,insert_logCurve]
  exact correctedPairedRealXi_deriv_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks hlk hl₁ hl₂
    T U WH Wu Hkeys Ukeys S cellCenter cellKey _ (e i).val
    (insert_positive I background _ hbackground (fun j => hx (e.symm j))) hH hu hx₁ hx₂ hcenter

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
