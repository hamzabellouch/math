import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightActualDeriv
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCounts
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRelativeInduction

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistoryOccurrenceVariables InitialCoordinatesTemplate
variable {ι : Type*}

theorem TreeDerivativeBudget.mono {outside : List ℕ} {x : ι → ℝ} {K B C : ℝ}
    {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (he : TreeDerivativeBudget outside x K B h e) (hBC : B ≤ C) :
    TreeDerivativeBudget outside x K C h e := by
  induction h with
  | leaf a => exact ⟨he.1,he.2.1.trans hBC,he.2.2.trans hBC⟩
  | node a p u hp hm left right il ir => exact
      ⟨he.1,he.2.1.trans hBC,il e.2.1 he.2.2.1,ir e.2.2 he.2.2.2⟩

def sourceHistoryBudget (V : ℕ → ℕ) (b k l : ℕ) (tb : ℝ) (center : ℕ → ℝ) : ℝ :=
  (historyCostCoefficient k*(b+1):ℕ) * (sourceCancellationBound V b k tb center l)^l

theorem sourceHistoryBudget_nonneg (V : ℕ → ℕ) (b k l : ℕ) (tb : ℝ) (center : ℕ → ℝ) :
    0 ≤ sourceHistoryBudget V b k l tb center := by
  unfold sourceHistoryBudget
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
    (zero_le_one.trans (sourceCancellationBound_one_le V b k tb center l)) _)

theorem actualRealHistoryScalar_deriv_le_sourceRanges (b s k : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside) [DecidableEq (Key h)]
    (hlk : l ≤ k) (hlabels : TreeSourceLabels (Template.initial (2*b) k) h)
    (x : Key h → ℝ) (i : Key h) (hx : SourceDomain b k G center h x)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ j,topCenters b center h j)+
      (∑ h,∑ j : Fin k,∑ r,compensationCenters b center h j r)) :
    ‖deriv (fun t => actualRealHistoryScalar b s X tb td G outside h hs (Expr.logCurve x i t)) 0‖ ≤
      (sourceLeafAmplitude k Δ E)^(2^l) * historyDerivativeCount l *
        actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center) := by
  apply actualRealHistoryScalar_deriv_le_of_budget b s k X tb td G Δ E
    (sourceCancellationBound V b k tb center l) _ center outside hX houtside hout
    (sourceCancellationBound_one_le V b k tb center l) (sourceHistoryBudget_nonneg V b k l tb center)
    h hs x i hx hcenter
  intro hsupport
  apply TreeDerivativeBudget.mono h (symbolicHistory h hs)
    (symbolicHistory_source_derivativeBudget b s k tb td G center h hs hlabels x hx.positive houtside
      hx.source hx.giant hsupport)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlabels.cost_le hlk)
    (pow_nonneg (zero_le_one.trans (sourceCancellationBound_one_le V b k tb center l)) _)

theorem actualRealXi_shared_deriv_le_sourceRanges (b s k : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    [DecidableEq (Key h₁)] [DecidableEq (Key h₂)] (hlk : l ≤ k)
    (hl₁ : TreeSourceLabels (Template.initial (2*b) k) h₁)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k) h₂)
    (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ) (i₁ : Key h₁) (i₂ : Key h₂)
    (hx₁ : SourceDomain b k G center h₁ x₁) (hx₂ : SourceDomain b k G center h₂ x₂)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ j,topCenters b center h j)+
      (∑ h,∑ j : Fin k,∑ r,compensationCenters b center h j r)) :
    ‖deriv (fun t => actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂
      (Expr.logCurve x₁ i₁ t) (Expr.logCurve x₂ i₂ t)) 0‖ ≤
      2*Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E) * historyDerivativeCount l *
        actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center) := by
  apply actualRealXi_shared_deriv_le_of_budget b s k X tb td G Δ E
    (sourceCancellationBound V b k tb center l) _ center outside hX houtside hout
    (sourceCancellationBound_one_le V b k tb center l) (sourceHistoryBudget_nonneg V b k l tb center)
    h₁ h₂ hs₁ hs₂ x₁ x₂ i₁ i₂ hx₁ hx₂ hcenter
  · intro hsupport
    apply TreeDerivativeBudget.mono h₁ (symbolicHistory h₁ hs₁)
      (symbolicHistory_source_derivativeBudget b s k tb td G center h₁ hs₁ hl₁ x₁ hx₁.positive houtside
        hx₁.source hx₁.giant hsupport)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hl₁.cost_le hlk)
      (pow_nonneg (zero_le_one.trans (sourceCancellationBound_one_le V b k tb center l)) _)
  · intro hsupport
    apply TreeDerivativeBudget.mono h₂ (symbolicHistory h₂ hs₂)
      (symbolicHistory_source_derivativeBudget b s k tb td G center h₂ hs₂ hl₂ x₂ hx₂.positive houtside
        hx₂.source hx₂.giant hsupport)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hl₂.cost_le hlk)
      (pow_nonneg (zero_le_one.trans (sourceCancellationBound_one_le V b k tb center l)) _)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
