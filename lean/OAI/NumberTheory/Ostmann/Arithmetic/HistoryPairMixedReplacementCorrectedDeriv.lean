import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open HistoryRepeatedSmoothPullback
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem correctedPairedRealXi_deriv_le (b s k₀ : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (hX : 0 < X) (houtside : ∀q ∈ outside,0 < q)
    (hout : outside.length = 2*s) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hlk : l ≤ k₀) (hl₁ : TreeSourceLabels (Template.initial (2*b) k₀) h)
    (hl₂ : TreeSourceLabels (Template.initial (2*b) k₀) k) {τ : Type}
    (T U WH Wu : ℝ) (Hkeys Ukeys : List (PairKey h k))
    (S : Finset τ) (cellCenter : τ → ℝ) (cellKey : τ → PairKey h k)
    (x : PairKey h k → ℝ) (j : PairKey h k) (hx : ∀i,0 < x i)
    (hH : T-WH ≤ Real.log ((Hkeys.map x).prod))
    (hu : Real.log ((Ukeys.map x).prod) ≤ U+Wu)
    (hx₁ : SourceDomain b k₀ G center h (fun i => x (leftMap h k i)))
    (hx₂ : SourceDomain b k₀ G center k (fun i => x (rightMap h k i)))
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑a,∑i,topCenters b center a i)+
      (∑a,∑j : Fin k₀,∑i,compensationCenters b center a j i)) :
    ‖deriv (fun t => correctedPairedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys
      S cellCenter cellKey (Expr.logCurve x j t)) 0‖ ≤
      correctedPairDerivativeBound WH Wu Hkeys.length Ukeys.length S.card h k V b k₀ tb Δ E center := by
  let c : ℝ → ℝ := fun t => rootCounterpart T U Hkeys Ukeys S cellCenter cellKey (Expr.logCurve x j t)
  let F : ℝ → ℂ := fun t => pairedRealXi b s X tb td G h k hs ks (Expr.logCurve x j t)
  let R := Real.exp (WH+Wu)
  let M := Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E)
  let A := (Hkeys.length:ℝ)+Ukeys.length+rootCounterpartDerivativeConstant*S.card
  let D := pairDerivativeBound h k V b k₀ tb Δ E center
  have hA : 0 ≤ A := by dsimp only [A]; positivity [rootCounterpartDerivativeConstant_pos]
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hc : DifferentiableAt ℝ c 0 :=
    rootCounterpart_logCurve_differentiableAt T U Hkeys Ukeys S cellCenter cellKey x j hx
  have hf : DifferentiableAt ℝ F 0 := by
    exact differentiableAt_logCurve_comp (pairedRealXi b s X tb td G h k hs ks) id x j hx
      ((pairedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks).differentiable (by simp) _)
  have hc0 : |c 0| ≤ R := by
    simpa only [c,Expr.logCurve_zero,R] using
      rootCounterpart_abs_le T U WH Wu Hkeys Ukeys S cellCenter cellKey x hx hH hu
  have hcd : |deriv c 0| ≤ R*A :=
    (Classical.choose_spec rootCounterpart_logCurve_deriv_bound).2 T U WH Wu Hkeys Ukeys S cellCenter cellKey x j hx hH hu
  have hf0 : ‖F 0‖ ≤ M := by
    simpa only [F,Expr.logCurve_zero,M] using
      pairedRealXi_norm_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks x hx₁ hx₂ hcenter
  have hfd : ‖deriv F 0‖ ≤ D :=
    pairedRealXi_deriv_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks hlk hl₁ hl₂ x j hx hx₁ hx₂ hcenter
  change ‖deriv (fun t => (c t:ℂ)*F t) 0‖ ≤ R*(D+M*A)
  rw [(hc.hasDerivAt.ofReal_comp.fun_mul hf.hasDerivAt).deriv]
  calc
    _ ≤ |deriv c 0| *‖F 0‖+|c 0| *‖deriv F 0‖ := by
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
        norm_add_le (((deriv c 0:ℝ):ℂ)*F 0) ((c 0:ℂ)*deriv F 0)
    _ ≤ (R*A)*M+R*D := add_le_add
      (mul_le_mul hcd hf0 (norm_nonneg _) (mul_nonneg hR hA))
      (mul_le_mul hc0 hfd (norm_nonneg _) hR)
    _ = _ := by ring

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
