import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightQuantitative
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRootCounterpart

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Characters.RationalHistory
open scoped ContDiff

def rootCounterpartDerivativeConstant : ℝ := Classical.choose rootCounterpart_logCurve_deriv_bound

theorem rootCounterpartDerivativeConstant_pos : 0 < rootCounterpartDerivativeConstant :=
  (Classical.choose_spec rootCounterpart_logCurve_deriv_bound).1

theorem rootCounterpart_logCurve_differentiableAt {κ ι : Type} [Fintype κ] [DecidableEq κ]
    (T U : ℝ) (Hkeys Ukeys : List κ) (S : Finset ι) (center : ι → ℝ) (cellKey : ι → κ)
    (x : κ → ℝ) (j : κ) (hx : ∀ i, 0 < x i) :
    DifferentiableAt ℝ (fun t => rootCounterpart T U Hkeys Ukeys S center cellKey
      (Expr.logCurve x j t)) 0 := by
  have hprod (keys : List κ) : ContDiffAt ℝ ∞ (fun y : κ → ℝ => (keys.map y).prod) x := by
    simpa only [keyProduct_realEval] using (keyProduct keys).contDiffAt_realEval x
      (Expr.RelativeControl.regular _ x 1 (keyProduct_relativeControl keys x hx))
  have hf : ContDiffAt ℝ ∞ (rootCounterpart T U Hkeys Ukeys S center cellKey) x := by
    apply counterpartArchimedean_contDiffAt T U _ _ S center _ x (hprod Hkeys) (hprod Ukeys)
    · intro i hi
      fun_prop
    · exact (keyProduct_pos Hkeys x hx).ne'
  have hf' : ContDiffAt ℝ ∞ (rootCounterpart T U Hkeys Ukeys S center cellKey) (Expr.logCurve x j 0) := by
    simpa only [Expr.logCurve_zero] using hf
  exact (hf'.comp 0 (HistorySymbolicEncoding.logCurve_contDiff x j).contDiffAt).differentiableAt (by simp)

namespace HistorySymbolicEncoding
open Construction HistoryOccurrenceVariables InitialCoordinatesTemplate

def correctedActualRealXi {κ ι : Type} (T U : ℝ) (Hkeys Ukeys : List κ)
    (S : Finset ι) (cellCenter : ι → ℝ) (cellKey : ι → κ) (x : κ → ℝ)
    (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ) : ℂ :=
  (rootCounterpart T U Hkeys Ukeys S cellCenter cellKey x:ℂ)*
    actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂

theorem correctedActualRealXi_shared_deriv_le {κ ι : Type} [Fintype κ] [DecidableEq κ]
    (T U WH Wu : ℝ) (Hkeys Ukeys : List κ) (S : Finset ι)
    (cellCenter : ι → ℝ) (cellKey : ι → κ) (x : κ → ℝ) (j : κ)
    (hx : ∀ i, 0 < x i) (hH : T-WH ≤ Real.log ((Hkeys.map x).prod))
    (hu : Real.log ((Ukeys.map x).prod) ≤ U+Wu)
    (b s k : ℕ) (X tb td G Δ E : ℝ) (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    [DecidableEq (Key h₁)] [DecidableEq (Key h₂)] (hlk : l ≤ k)
    (hl₁ : TreeSourceLabels (Template.initial (2*b) k) h₁)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k) h₂)
    (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ) (i₁ : Key h₁) (i₂ : Key h₂)
    (hx₁ : SourceDomain b k G center h₁ x₁) (hx₂ : SourceDomain b k G center h₂ x₂)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ i,topCenters b center h i)+
      (∑ h,∑ i : Fin k,∑ r,compensationCenters b center h i r)) :
    ‖deriv (fun t => correctedActualRealXi T U Hkeys Ukeys S cellCenter cellKey (Expr.logCurve x j t)
      b s X tb td G outside h₁ h₂ hs₁ hs₂ (Expr.logCurve x₁ i₁ t) (Expr.logCurve x₂ i₂ t)) 0‖ ≤
      Real.exp (WH+Wu) * Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E) *
        ((Hkeys.length:ℝ)+(Ukeys.length:ℝ)+rootCounterpartDerivativeConstant*S.card+
          2*historyDerivativeCount l*actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center)) := by
  let c (t : ℝ) := rootCounterpart T U Hkeys Ukeys S cellCenter cellKey (Expr.logCurve x j t)
  let F (t : ℝ) := actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂ (Expr.logCurve x₁ i₁ t) (Expr.logCurve x₂ i₂ t)
  let M := Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k E)
  let R := Real.exp (WH+Wu)
  let A := (Hkeys.length:ℝ)+(Ukeys.length:ℝ)+rootCounterpartDerivativeConstant*S.card
  let B := 2*historyDerivativeCount l*actualSourceDerivativeRate (sourceHistoryBudget V b k l tb center)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hM : 0 ≤ M := (Real.exp_pos _).le
  have hA : 0 ≤ A := by dsimp only [A]; positivity [rootCounterpartDerivativeConstant_pos]
  have hc := rootCounterpart_logCurve_differentiableAt T U Hkeys Ukeys S cellCenter cellKey x j hx
  have hf₁ := actualRealHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside h₁ hs₁ x₁ i₁ hx₁.positive
  have hf₂ := actualRealHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside h₂ hs₂ x₂ i₂ hx₂.positive
  have hF : DifferentiableAt ℝ F 0 := (hf₁.hasDerivAt.fun_mul hf₂.hasDerivAt.star).differentiableAt
  have hc0 : |c 0| ≤ R := by
    simpa only [c,Expr.logCurve_zero,R] using rootCounterpart_abs_le T U WH Wu Hkeys Ukeys S cellCenter cellKey x hx hH hu
  have hcd : |deriv c 0| ≤ R*A :=
    (Classical.choose_spec rootCounterpart_logCurve_deriv_bound).2 T U WH Wu Hkeys Ukeys S cellCenter cellKey x j hx hH hu
  have hF0 : ‖F 0‖ ≤ M := by
    simpa only [F,M,Expr.logCurve_zero] using actualRealXi_norm_le b s k X tb td G Δ E center outside hX houtside hout
      h₁ h₂ hs₁ hs₂ x₁ x₂ hx₁ hx₂ hcenter
  have hFd : ‖deriv F 0‖ ≤ M*B := by
    simpa only [F,M,B,mul_assoc,mul_left_comm,mul_comm] using
      actualRealXi_shared_deriv_le_sourceRanges b s k X tb td G Δ E center outside hX houtside hout
        h₁ h₂ hs₁ hs₂ hlk hl₁ hl₂ x₁ x₂ i₁ i₂ hx₁ hx₂ hcenter
  change ‖deriv (fun t => (c t:ℂ)*F t) 0‖ ≤ R*M*(A+B)
  rw [(hc.hasDerivAt.ofReal_comp.fun_mul hF.hasDerivAt).deriv]
  calc
    _ ≤ |deriv c 0| *‖F 0‖+|c 0| *‖deriv F 0‖ := by
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
        norm_add_le (((deriv c 0:ℝ):ℂ)*F 0) ((c 0:ℂ)*deriv F 0)
    _ ≤ (R*A)*M+R*(M*B) := add_le_add
      (mul_le_mul hcd hF0 (norm_nonneg _) (mul_nonneg hR hA))
      (mul_le_mul hc0 hFd (norm_nonneg _) hR)
    _ = _ := by ring

end HistorySymbolicEncoding
end Ostmann.Arithmetic

end

end OAI
