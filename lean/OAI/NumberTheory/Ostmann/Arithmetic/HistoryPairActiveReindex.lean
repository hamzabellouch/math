import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActiveSourceDomain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairActiveXi

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open PrimeCellFreezing
open scoped ContDiff
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem reindex_logCurve {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (x : ι → ℝ) (i : ι) (t : ℝ) :
    (fun j => Expr.logCurve x i t (e.symm j)) =
      Expr.logCurve (fun j => x (e.symm j)) (e i) t := by
  funext j
  simp only [Expr.logCurve,Equiv.symm_apply_eq]

theorem reindex_mem_logRectangle {ι κ : Type*} (e : ι ≃ κ) (lo hi z : ι → ℝ)
    (hz : z∈logRectangle lo hi) :
    (fun j => z (e.symm j))∈logRectangle (fun j=>lo (e.symm j)) (fun j=>hi (e.symm j)) :=
  fun j _ => hz (e.symm j) (Set.mem_univ _)

def reindexedRealXi (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    {ι : Type*} (e : ι ≃ I) (x : ι → ℝ) : ℂ :=
  activeRealXi b s X tb td G h k hs ks I background (fun j => x (e.symm j))

theorem reindexedRealXi_log_contDiff (b s : ℕ) (X tb td G : ℝ) (hX : 0<X)
    (houtside : ∀q∈outside,0<q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    (hbackground : ∀i,0<background i) {ι : Type*} [Fintype ι] (e : ι ≃ I) :
    ContDiff ℝ ∞ (fun y : ι → ℝ => reindexedRealXi b s X tb td G h k hs ks I background e
      (fun i => Real.exp (y i))) :=
  (activeRealXi_log_contDiff b s X tb td G hX houtside h k hs ks I background hbackground).comp
    (show ContDiff ℝ ∞ (fun y : ι → ℝ => fun j : I => y (e.symm j)) by fun_prop)

theorem reindexedRealXi_deriv_le (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0<X) (houtside : ∀q∈outside,0<q)
    (hout : outside.length=2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hlk : l≤k₀) (hl₁ : TreeSourceLabels (Template.initial (2*b) k₀) h)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k₀) k)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    (hbackground : ∀i,0<background i) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ I) (x : ι → ℝ) (i : ι) (hx : ∀i,0<x i)
    (hx₁ : SourceDomain b k₀ G center h
      (fun i => insert I background (fun j=>x (e.symm j)) (leftMap h k i)))
    (hx₂ : SourceDomain b k₀ G center k
      (fun i => insert I background (fun j=>x (e.symm j)) (rightMap h k i)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑a,∑i,topCenters b center a i)+
      (∑a,∑j:Fin k₀,∑i,compensationCenters b center a j i)) :
    ‖deriv (fun t => reindexedRealXi b s X tb td G h k hs ks I background e (Expr.logCurve x i t)) 0‖ ≤
      pairDerivativeBound h k V b k₀ tb Δ E center := by
  unfold reindexedRealXi
  simp_rw [reindex_logCurve]
  exact activeRealXi_deriv_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks hlk hl₁ hl₂
    I background hbackground _ (e i) (fun j=>hx (e.symm j)) hx₁ hx₂ hcenter

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
