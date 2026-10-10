import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceXi
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightTreeDeriv

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
open InitialCoordinatesTemplate

theorem actualRealHistoryScalar_deriv_le_of_budget (b s k : ℕ) (X tb td G Δ E K B : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    (hK : 1 ≤ K) (hB : 0 ≤ B)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside) [DecidableEq (Key h)]
    (x : Key h → ℝ) (i : Key h) (hx : SourceDomain b k G center h x)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ j,topCenters b center h j)+
      (∑ h,∑ j : Fin k,∑ r,compensationCenters b center h j r))
    (hbudget : realHistorySupportWeight b s tb td G outside x h (symbolicHistory h hs) ≠ 0 →
      TreeDerivativeBudget outside x K B h (symbolicHistory h hs)) :
    ‖deriv (fun t => actualRealHistoryScalar b s X tb td G outside h hs (Expr.logCurve x i t)) 0‖ ≤
      (sourceLeafAmplitude k Δ E)^(2^l) * historyDerivativeCount l * actualSourceDerivativeRate B := by
  classical
  by_cases hz : realHistorySupportWeight b s tb td G outside x h (symbolicHistory h hs) = 0
  · have hd := encode_deriv_zero_of_support_zero b s X tb td G hX outside houtside h hs
      (rootExpr h) (compensationExpr h) x i hx.positive
      ⟨trivial,trivial,fun _ => trivial⟩ (fun j => ⟨Sum.inr (Sum.inl j),rfl⟩)
      (hx.positive _) (hx.positive _) (fun j => ⟨Sum.inr (Sum.inr j),rfl⟩) hz
    change ‖deriv (fun t => realHistoryScalar b s X tb td G outside (Expr.logCurve x i t)
      h (encode V outside h hs (rootExpr h) (compensationExpr h))) 0‖ ≤ _
    rw [hd,norm_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (sourceLeafAmplitude_pos k Δ E).le _)
      (historyDerivativeCount_nonneg l)) (actualSourceDerivativeRate_nonneg hB)
  · exact encode_deriv_le_on_source_support b s k X tb td G Δ E K B center outside
      (independentSlot h) x i hX hx.positive houtside hout hx.source hK hB hcenter h hs hx.leaves
      (rootExpr h) (compensationExpr h) (fun j => ⟨Sum.inr (Sum.inl j),rfl,rfl⟩)
      ⟨trivial,trivial,fun _ => trivial⟩ (fun j => ⟨Sum.inr (Sum.inr j),rfl,rfl⟩)
      (hx.positive _) (hx.positive _) (hx.giant false) (hx.giant true) (hbudget hz) hz

theorem actualRealHistoryScalar_logCurve_differentiableAt (b s : ℕ) (X tb td G : ℝ)
    (hX : 0 < X) (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside) [DecidableEq (Key h)]
    (x : Key h → ℝ) (i : Key h) (hx : ∀ j, 0 < x j) :
    DifferentiableAt ℝ (fun t => actualRealHistoryScalar b s X tb td G outside h hs
      (Expr.logCurve x i t)) 0 := by
  classical
  exact encode_realHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside h hs
    (rootExpr h) (compensationExpr h) x i ⟨trivial,trivial,fun _ => trivial⟩
    (fun j => hx _) (hx _) (hx _) (fun _ => trivial) (fun j => hx _)

theorem actualRealXi_shared_deriv_le_of_budget (b s k : ℕ) (X tb td G Δ E K B : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    (hK : 1 ≤ K) (hB : 0 ≤ B)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    [DecidableEq (Key h₁)] [DecidableEq (Key h₂)]
    (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ) (i₁ : Key h₁) (i₂ : Key h₂)
    (hx₁ : SourceDomain b k G center h₁ x₁) (hx₂ : SourceDomain b k G center h₂ x₂)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ j,topCenters b center h j)+
      (∑ h,∑ j : Fin k,∑ r,compensationCenters b center h j r))
    (hb₁ : realHistorySupportWeight b s tb td G outside x₁ h₁ (symbolicHistory h₁ hs₁) ≠ 0 →
      TreeDerivativeBudget outside x₁ K B h₁ (symbolicHistory h₁ hs₁))
    (hb₂ : realHistorySupportWeight b s tb td G outside x₂ h₂ (symbolicHistory h₂ hs₂) ≠ 0 →
      TreeDerivativeBudget outside x₂ K B h₂ (symbolicHistory h₂ hs₂)) :
    ‖deriv (fun t => actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂
      (Expr.logCurve x₁ i₁ t) (Expr.logCurve x₂ i₂ t)) 0‖ ≤
      2*Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E) *
        historyDerivativeCount l * actualSourceDerivativeRate B := by
  classical
  let F (t : ℝ) := actualRealHistoryScalar b s X tb td G outside h₁ hs₁ (Expr.logCurve x₁ i₁ t)
  let H (t : ℝ) := actualRealHistoryScalar b s X tb td G outside h₂ hs₂ (Expr.logCurve x₂ i₂ t)
  let A := (sourceLeafAmplitude k Δ E)^(2^l)
  let D := historyDerivativeCount l * actualSourceDerivativeRate B
  have hA : 0 ≤ A := pow_nonneg (sourceLeafAmplitude_pos k Δ E).le _
  have hD : 0 ≤ D := mul_nonneg (historyDerivativeCount_nonneg l) (actualSourceDerivativeRate_nonneg hB)
  have hF := actualRealHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside h₁ hs₁ x₁ i₁ hx₁.positive
  have hH := actualRealHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside h₂ hs₂ x₂ i₂ hx₂.positive
  have hFn : ‖F 0‖ ≤ A := by
    simpa only [F,Expr.logCurve_zero,A] using
      actualRealHistoryScalar_norm_le_sourceRanges b s k X tb td G Δ E center outside hX houtside hout
        h₁ hs₁ hx₁.leaves x₁ hx₁.positive hx₁.source hx₁.giant hcenter
  have hHn : ‖H 0‖ ≤ A := by
    simpa only [H,Expr.logCurve_zero,A] using
      actualRealHistoryScalar_norm_le_sourceRanges b s k X tb td G Δ E center outside hX houtside hout
        h₂ hs₂ hx₂.leaves x₂ hx₂.positive hx₂.source hx₂.giant hcenter
  have hFd : ‖deriv F 0‖ ≤ A*D := by
    simpa only [F,A,D,mul_assoc] using actualRealHistoryScalar_deriv_le_of_budget b s k X tb td G Δ E K B
      center outside hX houtside hout hK hB h₁ hs₁ x₁ i₁ hx₁ hcenter hb₁
  have hHd : ‖deriv H 0‖ ≤ A*D := by
    simpa only [H,A,D,mul_assoc] using actualRealHistoryScalar_deriv_le_of_budget b s k X tb td G Δ E K B
      center outside hX houtside hout hK hB h₂ hs₂ x₂ i₂ hx₂ hcenter hb₂
  change ‖deriv (fun t => F t*star (H t)) 0‖ ≤ _
  rw [(hF.hasDerivAt.fun_mul hH.hasDerivAt.star).deriv]
  calc
    _ ≤ ‖deriv F 0‖*‖H 0‖+‖F 0‖*‖deriv H 0‖ := by
      simpa only [norm_mul,norm_star] using norm_add_le (deriv F 0*star (H 0)) (F 0*star (deriv H 0))
    _ ≤ (A*D)*A+A*(A*D) := add_le_add
      (mul_le_mul hFd hHn (norm_nonneg _) (mul_nonneg hA hD))
      (mul_le_mul hFn hHd (norm_nonneg _) hA)
    _ = _ := by
      rw [← sourceLeafAmplitude_pair]
      dsimp only [A,D]
      ring

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
