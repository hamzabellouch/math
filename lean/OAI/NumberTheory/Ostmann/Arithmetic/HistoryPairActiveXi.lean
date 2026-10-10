import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActiveCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSmoothXi

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open scoped ContDiff
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def activeRealXi (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ) (x : I → ℝ) : ℂ :=
  pairedRealXi b s X tb td G h k hs ks (insert I background x)

theorem activeRealXi_log_contDiff (b s : ℕ) (X tb td G : ℝ) (hX : 0 < X)
    (houtside : ∀ q∈outside, 0 < q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    (hbackground : ∀ i, 0 < background i) :
    ContDiff ℝ ∞ (fun y : I → ℝ => activeRealXi b s X tb td G h k hs ks I background
      (fun i => Real.exp (y i))) :=
  log_contDiff_insert _ I background hbackground
    (pairedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks)

def pairDerivativeBound (h k : History l) (V : ℕ → ℕ) (b k₀ : ℕ)
    (tb Δ E : ℝ) (center : ℕ → ℝ) : ℝ :=
  ((Fintype.card (Key h):ℝ)+Fintype.card (Key k))*
    Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E)*historyDerivativeCount l*
      actualSourceDerivativeRate (sourceHistoryBudget V b k₀ l tb center)

theorem pairDerivativeBound_nonneg (h k : History l) (V : ℕ → ℕ) (b k₀ : ℕ)
    (tb Δ E : ℝ) (center : ℕ → ℝ) :
    0 ≤ pairDerivativeBound h k V b k₀ tb Δ E center := by
  apply mul_nonneg _ (actualSourceDerivativeRate_nonneg (sourceHistoryBudget_nonneg V b k₀ l tb center))
  exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (historyDerivativeCount_nonneg l)

theorem activeRealXi_deriv_le (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0 < X) (houtside : ∀ q∈outside, 0 < q)
    (hout : outside.length=2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hlk : l ≤ k₀) (hl₁ : TreeSourceLabels (Template.initial (2*b) k₀) h)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k₀) k)
    (I : Finset (PairKey h k)) (background : PairKey h k → ℝ)
    (hbackground : ∀ i, 0 < background i) (x : I → ℝ) (j : I) (hx : ∀ i, 0 < x i)
    (hx₁ : SourceDomain b k₀ G center h (fun i => insert I background x (leftMap h k i)))
    (hx₂ : SourceDomain b k₀ G center k (fun i => insert I background x (rightMap h k i)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ a,∑ i,topCenters b center a i)+
      (∑ a,∑ j : Fin k₀,∑ i,compensationCenters b center a j i)) :
    ‖deriv (fun t => activeRealXi b s X tb td G h k hs ks I background (Expr.logCurve x j t)) 0‖ ≤
      pairDerivativeBound h k V b k₀ tb Δ E center := by
  unfold activeRealXi
  simp_rw [insert_logCurve]
  exact pairedRealXi_deriv_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks
    hlk hl₁ hl₂ _ j.val (insert_positive I background x hbackground hx) hx₁ hx₂ hcenter

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
