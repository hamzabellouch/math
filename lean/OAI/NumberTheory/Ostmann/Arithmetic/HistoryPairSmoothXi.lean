import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedSmoothPullback
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPairSmooth
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightQuantitative

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryRepeatedSmoothPullback
open scoped ContDiff FourierTransform
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def pairedRealXi (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (x : PairKey h k → ℝ) : ℂ :=
  actualRealXi b s X tb td G outside h k hs ks
    (fun i => x (leftMap h k i)) (fun i => x (rightMap h k i))

theorem pairedRealXi_log_contDiff (b s : ℕ) (X tb td G : ℝ) (hX : 0 < X)
    (houtside : ∀ q∈outside, 0 < q) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) :
    ContDiff ℝ ∞ (fun y : PairKey h k → ℝ =>
      pairedRealXi b s X tb td G h k hs ks (fun i => Real.exp (y i))) := by
  exact (actualRealXi_log_contDiff b s X tb td G hX outside houtside h k hs ks).comp
    (show ContDiff ℝ ∞ (fun y : PairKey h k → ℝ =>
      ((fun i => y (leftMap h k i)),(fun i => y (rightMap h k i)))) by fun_prop)

theorem pairedRealXi_integer_sample (b s : ℕ) (X tb td G : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k) :
    pairedRealXi b s X tb td G h k hs ks (fun i => (pairSample h k i:ℝ)) =
      smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
        outside smoothPartition G h *
      star (smoothHistoryScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td)
        outside smoothPartition G k) := by
  simpa only [pairedRealXi,leftMap_sample,rightMap_sample h k hroot] using
    actualRealXi_integer_sample b s X tb td G outside h k hs ks

theorem pairedRealXi_norm_le (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0 < X) (houtside : ∀ q∈outside, 0 < q)
    (hout : outside.length=2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (x : PairKey h k → ℝ)
    (hx₁ : SourceDomain b k₀ G center h (fun i => x (leftMap h k i)))
    (hx₂ : SourceDomain b k₀ G center k (fun i => x (rightMap h k i)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ a,∑ i,topCenters b center a i)+
      (∑ a,∑ j : Fin k₀,∑ i,compensationCenters b center a j i)) :
    ‖pairedRealXi b s X tb td G h k hs ks x‖ ≤
      Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E) :=
  actualRealXi_norm_le b s k₀ X tb td G Δ E center outside hX houtside hout
    h k hs ks _ _ hx₁ hx₂ hcenter

theorem pairedRealXi_deriv_le (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0 < X) (houtside : ∀ q∈outside, 0 < q)
    (hout : outside.length=2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hlk : l ≤ k₀) (hl₁ : TreeSourceLabels (Template.initial (2*b) k₀) h)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k₀) k)
    (x : PairKey h k → ℝ) (j : PairKey h k) (hx : ∀ i, 0 < x i)
    (hx₁ : SourceDomain b k₀ G center h (fun i => x (leftMap h k i)))
    (hx₂ : SourceDomain b k₀ G center k (fun i => x (rightMap h k i)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ a,∑ i,topCenters b center a i)+
      (∑ a,∑ j : Fin k₀,∑ i,compensationCenters b center a j i)) :
    ‖deriv (fun t => pairedRealXi b s X tb td G h k hs ks (Expr.logCurve x j t)) 0‖ ≤
      ((Fintype.card (Key h):ℝ)+Fintype.card (Key k))*
        Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E)*historyDerivativeCount l*
          actualSourceDerivativeRate (sourceHistoryBudget V b k₀ l tb center) := by
  classical
  let a : ℝ := (sourceLeafAmplitude k₀ Δ E)^(2^l)
  let R : ℝ := historyDerivativeCount l*actualSourceDerivativeRate (sourceHistoryBudget V b k₀ l tb center)
  let F₁ : ℝ → ℂ := fun t => actualRealHistoryScalar b s X tb td G outside h hs
    (fun i => Expr.logCurve x j t (leftMap h k i))
  let F₂ : ℝ → ℂ := fun t => actualRealHistoryScalar b s X tb td G outside k ks
    (fun i => Expr.logCurve x j t (rightMap h k i))
  have ha : 0 ≤ a := pow_nonneg (sourceLeafAmplitude_pos k₀ Δ E).le _
  have hR : 0 ≤ R := mul_nonneg (historyDerivativeCount_nonneg l)
    (actualSourceDerivativeRate_nonneg (sourceHistoryBudget_nonneg V b k₀ l tb center))
  have hf₁ := (actualRealHistoryScalar_log_contDiff b s X tb td G hX outside houtside h hs).differentiable (by simp)
  have hf₂ := (actualRealHistoryScalar_log_contDiff b s X tb td G hX outside houtside k ks).differentiable (by simp)
  have hd₁ : ‖deriv F₁ 0‖ ≤ (Fintype.card (Key h):ℝ)*(a*R) := by
    apply deriv_logCurve_comp_le _ (leftMap h k) x j hx (mul_nonneg ha hR) (hf₁ _)
    intro i
    simpa only [a,R,mul_assoc] using actualRealHistoryScalar_deriv_le_sourceRanges
      b s k₀ X tb td G Δ E center outside hX houtside hout h hs hlk hl₁ _ i hx₁ hcenter
  have hd₂ : ‖deriv F₂ 0‖ ≤ (Fintype.card (Key k):ℝ)*(a*R) := by
    apply deriv_logCurve_comp_le _ (rightMap h k) x j hx (mul_nonneg ha hR) (hf₂ _)
    intro i
    simpa only [a,R,mul_assoc] using actualRealHistoryScalar_deriv_le_sourceRanges
      b s k₀ X tb td G Δ E center outside hX houtside hout k ks hlk hl₂ _ i hx₂ hcenter
  have hn₁ : ‖F₁ 0‖ ≤ a := by
    simpa only [F₁,Expr.logCurve_zero,a] using actualRealHistoryScalar_norm_le_sourceRanges
      b s k₀ X tb td G Δ E center outside hX houtside hout h hs hx₁.leaves
      _ hx₁.positive hx₁.source hx₁.giant hcenter
  have hn₂ : ‖F₂ 0‖ ≤ a := by
    simpa only [F₂,Expr.logCurve_zero,a] using actualRealHistoryScalar_norm_le_sourceRanges
      b s k₀ X tb td G Δ E center outside hX houtside hout k ks hx₂.leaves
      _ hx₂.positive hx₂.source hx₂.giant hcenter
  have hc₁ : DifferentiableAt ℝ F₁ 0 :=
    differentiableAt_logCurve_comp _ (leftMap h k) x j hx (hf₁ _)
  have hc₂ : DifferentiableAt ℝ F₂ 0 :=
    differentiableAt_logCurve_comp _ (rightMap h k) x j hx (hf₂ _)
  change ‖deriv (fun t => F₁ t*star (F₂ t)) 0‖ ≤ _
  rw [(hc₁.hasDerivAt.fun_mul hc₂.hasDerivAt.star).deriv]
  calc
    _ ≤ ‖deriv F₁ 0‖*‖F₂ 0‖+‖F₁ 0‖*‖deriv F₂ 0‖ := by
      simpa only [norm_mul,norm_star] using
        norm_add_le (deriv F₁ 0*star (F₂ 0)) (F₁ 0*star (deriv F₂ 0))
    _ ≤ ((Fintype.card (Key h):ℝ)*(a*R))*a+a*((Fintype.card (Key k):ℝ)*(a*R)) :=
      add_le_add (mul_le_mul hd₁ hn₂ (norm_nonneg _) (by positivity))
        (mul_le_mul hn₁ hd₂ (norm_nonneg _) ha)
    _ = _ := by rw [← sourceLeafAmplitude_pair]; dsimp only [a,R]; ring

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
