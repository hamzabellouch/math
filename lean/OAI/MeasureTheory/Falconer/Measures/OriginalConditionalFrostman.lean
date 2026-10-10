import OAI.MeasureTheory.Falconer.Recursion.ProfileIncrementFrostman

namespace OAI

/-! # Conditional source-ball estimates before changing the original coordinates -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_original_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^t ≤ r → r ≤ 1/(2:ℝ)^p →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam)*((2:ℝ)^p*r)^s) := by
  intro x r hr hr1
  have hpow : 0 < (2:ℝ)^p := by positivity
  have hscale : (2:ℝ)^p*(1/(2:ℝ)^t) = 1/(2:ℝ)^(t-p) := by
    conv_lhs => rw [show t = p+(t-p) by omega,pow_add]
    field_simp
  have hlo : 1/(2:ℝ)^(t-p) ≤ (2:ℝ)^p*r := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hr hpow.le
  have hhi : (2:ℝ)^p*r ≤ 1 := by
    calc
      _ ≤ (2:ℝ)^p*(1/(2:ℝ)^p) := mul_le_mul_of_nonneg_left hr1 hpow.le
      _ = 1 := by field_simp
  have hh := sourceClass_conditional_frostman_of_increment Q hQ μ hN hB hs hwidth hlarge
    hp₀ hpt htN hP hPpos hinc (cellScaleMap p (Q.descendant P).center x) ((2:ℝ)^p*r) hlo hhi
  rw [rescaled_conditional_ball_apply] at hh
  have hc : (Q.descendant P).center+((2:ℝ)^p)⁻¹ • cellScaleMap p (Q.descendant P).center x = x := by
    simp only [cellScaleMap,smul_smul,inv_mul_cancel₀ hpow.ne',one_smul]
    abel
  have hrad : ((2:ℝ)^p*r)/(2:ℝ)^p = r := by field_simp
  rwa [hc,hrad] at hh

theorem sourceClass_original_conditional_frostman_power (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E η : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) ≤ ((2:ℝ)^N)^η) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^t ≤ r → r ≤ 1/(2:ℝ)^p →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier (ball x r) ≤
        ENNReal.ofReal (((2:ℝ)^N)^η*((2:ℝ)^p*r)^s) := by
  intro x r hr hr1
  apply (sourceClass_original_conditional_frostman Q hQ μ hN hB hs hwidth hlarge hp₀
    hpt htN hP hPpos hinc x r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^t).trans hr
  exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) _)

end Falconer.Regularization

end OAI
