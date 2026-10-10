import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightQuantitative
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistoryOccurrenceVariables InitialCoordinatesTemplate
open HistoryProductWindows Conclusion
open scoped FourierTransform SchwartzMap

def sourceDerivativeCoefficient : ℝ :=
  leafProfileBound (𝓕 SchwartzCutoff.psi)+2*partitionDerivativeConstant+cellDerivativeConstant

theorem sourceDerivativeCoefficient_pos : 0 < sourceDerivativeCoefficient := by
  have hp := leafProfileBound_pos (𝓕 SchwartzCutoff.psi)
  have hφ := partitionDerivativeConstant_pos
  have hc := cellDerivativeConstant_pos
  unfold sourceDerivativeCoefficient
  positivity

def sourceAmplitudeCeiling (k : ℕ) (E : ℝ) : ℝ :=
  max 1 (leafFourierBound*Real.exp ((E+12+4*(k:ℝ))/2))

def sourceDerivativePrefactor (k : ℕ) (E : ℝ) : ℝ :=
  2*(sourceAmplitudeCeiling k E)^(2^(k+1))*(2:ℝ)^(k+1)*
    (2*(historyCostCoefficient k:ℝ))*sourceDerivativeCoefficient

theorem sourceDerivativePrefactor_pos (k : ℕ) (E : ℝ) :
    0 < sourceDerivativePrefactor k E := by
  have hA : 0 < sourceAmplitudeCeiling k E := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hN : 0 < (historyCostCoefficient k:ℝ) := by exact_mod_cast historyCostCoefficient_pos k
  have hC := sourceDerivativeCoefficient_pos
  unfold sourceDerivativePrefactor
  positivity

theorem linear_prefactor_mul_exp_le (P C m : ℝ) (hP : 0 < P) (_hC : 0 ≤ C) (hm : 1 ≤ m) :
    P*m*Real.exp (C*m) ≤ Real.exp ((|Real.log P|+1+C)*m) := by
  have hp : P ≤ Real.exp (|Real.log P| *m) := by
    calc
      P = Real.exp (Real.log P) := (Real.exp_log hP).symm
      _ ≤ _ := Real.exp_le_exp.mpr ((le_abs_self _).trans
        (le_mul_of_one_le_right (abs_nonneg (Real.log P)) hm))
  have hme : m ≤ Real.exp m := (Real.add_one_le_exp m).trans' (by linarith)
  calc
    _ ≤ Real.exp (|Real.log P| *m)*Real.exp m*Real.exp (C*m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hp hme (by linarith) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring

theorem source_pair_derivative_budget_le (b k l : ℕ) (Δ E K C m : ℝ)
    (hl : l ≤ k) (hΔ : 0 ≤ Δ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hb : (b:ℝ) ≤ m) (hKe : K ≤ Real.exp (C*m)) :
    2*((sourceLeafAmplitude k Δ E)^(2^l)*(sourceLeafAmplitude k Δ E)^(2^l))*
      historyDerivativeCount l * actualSourceDerivativeRate
        ((historyCostCoefficient k*(b+1):ℕ)*K^l) ≤
      sourceDerivativePrefactor k E*m*Real.exp ((C*(k:ℝ))*m) := by
  let A := sourceAmplitudeCeiling k E
  have hA : 1 ≤ A := le_max_left _ _
  have hleaf : sourceLeafAmplitude k Δ E ≤ A := by
    apply le_trans _ (le_max_right _ _)
    unfold sourceLeafAmplitude
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) leafFourierBound_pos.le
  have hpow : 2^l ≤ (2^k:ℕ) := Nat.pow_le_pow_right (by omega) hl
  have hp : (sourceLeafAmplitude k Δ E)^(2^l) ≤ A^(2^k) :=
    (pow_le_pow_left₀ (sourceLeafAmplitude_pos k Δ E).le hleaf _).trans (pow_le_pow_right₀ hA hpow)
  have hpair : (sourceLeafAmplitude k Δ E)^(2^l)*(sourceLeafAmplitude k Δ E)^(2^l) ≤ A^(2^(k+1)) := by
    have hh := mul_le_mul hp hp (pow_nonneg (sourceLeafAmplitude_pos k Δ E).le _) (pow_nonneg (zero_le_one.trans hA) _)
    simpa only [← pow_add,pow_succ,Nat.mul_two] using hh
  have hcount : historyDerivativeCount l ≤ (2:ℝ)^(k+1) := by
    unfold historyDerivativeCount
    exact (sub_le_self _ zero_le_one).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hKpow : K^l ≤ Real.exp ((C*(k:ℝ))*m) := by
    calc
      _ ≤ (Real.exp (C*m))^l := pow_le_pow_left₀ (zero_le_one.trans hK) hKe _
      _ = Real.exp ((l:ℝ)*(C*m)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hl' : (l:ℝ) ≤ k := by exact_mod_cast hl
        have hm0 : 0 ≤ m := by linarith
        have he := mul_le_mul_of_nonneg_right hl' (mul_nonneg hC hm0)
        nlinarith [he])
  have hN : (historyCostCoefficient k*(b+1):ℕ) ≤ (2*(historyCostCoefficient k:ℝ))*m := by
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hnon := Nat.cast_nonneg (historyCostCoefficient k) (α := ℝ)
    nlinarith
  have hB : ((historyCostCoefficient k*(b+1):ℕ):ℝ)*K^l ≤
      ((2*(historyCostCoefficient k:ℝ))*m)*Real.exp ((C*(k:ℝ))*m) :=
    mul_le_mul hN hKpow (pow_nonneg (zero_le_one.trans hK) _) (by positivity)
  change 2*_ * _ * (_*sourceDerivativeCoefficient) ≤ _
  calc
    _ ≤ 2*A^(2^(k+1))*(2:ℝ)^(k+1)*
        ((((2*(historyCostCoefficient k:ℝ))*m)*Real.exp ((C*(k:ℝ))*m))*sourceDerivativeCoefficient) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hpair (by norm_num)) hcount
        (historyDerivativeCount_nonneg l) (by positivity))
        (mul_le_mul_of_nonneg_right hB sourceDerivativeCoefficient_pos.le)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hK) _)) sourceDerivativeCoefficient_pos.le)
        (by positivity)
    _ = _ := by unfold sourceDerivativePrefactor; dsimp only [A]; ring

theorem exists_actualRealXi_derivative_exp_bound (Bs BD Bz E : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b s : ℕ) (L X tb td G J : ℝ) (center : ℕ → ℝ) (outside : List ℕ),
      1 ≤ bulkSize k L → (b:ℝ) ≤ bulkSize k L → 0 ≤ initialGap Bs k L →
      0 < X → (∀ q ∈ outside, 0 < q) → outside.length=2*s →
      |(∑ h,∑ j,topCenters b center h j)-(J-2*tb)| ≤ 2 →
      (∀ j<k, |typeCenter b j center-nominalWeight k J (stepGap BD Bz k L) j| ≤ 2) →
      Real.log X+initialGap Bs k L-E ≤ 2*G+2*tb+2*td+
        (∑ h,∑ j,topCenters b center h j)+(∑ h,∑ j : Fin k,∑ r,compensationCenters b center h j r) →
      ∀ (l : ℕ), l ≤ k → ∀ (h₁ h₂ : History l)
        (hs₁ : h₁.Supported (Conclusion.frequencyBound Bs BD Bz k L) outside)
        (hs₂ : h₂.Supported (Conclusion.frequencyBound Bs BD Bz k L) outside)
        [DecidableEq (Key h₁)] [DecidableEq (Key h₂)],
      TreeSourceLabels (Template.initial (2*b) k) h₁ → TreeSourceLabels (Template.initial (2*b) k) h₂ →
      ∀ (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ) (i₁ : Key h₁) (i₂ : Key h₂),
      SourceDomain b k G center h₁ x₁ → SourceDomain b k G center h₂ x₂ →
      ‖deriv (fun t => actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂
        (Expr.logCurve x₁ i₁ t) (Expr.logCurve x₂ i₂ t)) 0‖ ≤ Real.exp (C*(bulkSize k L:ℝ)) := by
  obtain ⟨CK,hCK,hKb⟩ := exists_sourceCancellationBound_le_exp_linear Bs BD Bz k
  let P := sourceDerivativePrefactor k E
  refine ⟨|Real.log P|+1+CK*(k:ℝ),by positivity,?_⟩
  intro b s L X tb td G J center outside hm hb hΔ hX houtside hout htop htypes hcenter l hl
    h₁ h₂ hs₁ hs₂ _ _ hl₁ hl₂ x₁ x₂ i₁ i₂ hx₁ hx₂
  have hd := actualRealXi_shared_deriv_le_sourceRanges b s k X tb td G (initialGap Bs k L) E center outside
    hX houtside hout h₁ h₂ hs₁ hs₂ hl hl₁ hl₂ x₁ x₂ i₁ i₂ hx₁ hx₂ hcenter
  rw [← sourceLeafAmplitude_pair] at hd
  have hb' := source_pair_derivative_budget_le b k l (initialGap Bs k L) E
    (sourceCancellationBound (Conclusion.frequencyBound Bs BD Bz k L) b k tb center l) CK (bulkSize k L)
    hl hΔ (sourceCancellationBound_one_le _ _ _ _ _ _) hCK.le (by exact_mod_cast hm) hb
    (hKb b L tb J center hm l hl htop htypes)
  exact hd.trans (hb'.trans (linear_prefactor_mul_exp_le P (CK*(k:ℝ)) (bulkSize k L)
    (sourceDerivativePrefactor_pos k E) (mul_nonneg hCK.le (Nat.cast_nonneg _)) (by exact_mod_cast hm)))

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
