import OAI.MeasureTheory.Falconer.Recursion.ProfileBalls
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-!
# Full conditional class laws, normalized by the actual cell mass

The profile is only a comparison for that mass. The conditional measure
is the original restricted class law divided by its own cell mass.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem conditional_real_le (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (A T : Set (Space d)) :
    (ProbabilityTheory.cond ρ A T).toReal ≤ (ρ T).toReal/(ρ A).toReal := by
  unfold ProbabilityTheory.cond
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hh : ((ρ.restrict A) T).toReal ≤ (ρ T).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show 0 ≤ (ρ A).toReal from ENNReal.toReal_nonneg))

theorem sourceClass_conditional_probability (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N B : ℕ)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N) (P : CellPath d)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier) :
    IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  exact ProbabilityTheory.cond_isProbabilityMeasure hPpos.ne'

theorem sourceClass_conditional_ball_upper (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p n : ℕ} (hpN : p ≤ N) (hn : n ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
      (ball x (C*(Q.side/(2:ℝ)^n)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ n+2*((d:ℝ)+1)*lam) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  let c : ℝ := ((d:ℝ)+1)*lam
  let mp := sourceProfile Q μ N B p₀ p
  let mn := sourceProfile Q μ N B p₀ n
  let D : ℝ := ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)
  have hRp : 0 < R := by dsimp [R]; positivity
  have hb := sourceClass_ball_upper Q hQ μ hN hB hwidth hlarge hp₀ hn x hC
  have hl := (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hpN hP hPpos).1
  have hc := conditional_real_le (sourceClass Q μ N B p₀) (Q.descendant P).carrier
    (ball x (C*(Q.side/(2:ℝ)^n)))
  have hratio := div_le_div₀ (show 0 ≤ D*(R^c*R^(-mn)) by dsimp [D]; positivity)
    hb (show 0 < R^(-c)*R^(-mp) by positivity) (show R^(-c)*R^(-mp) ≤
      (sourceClass Q μ N B p₀ (Q.descendant P).carrier).toReal by
        simpa only [c,mp,R,neg_mul] using hl)
  apply (hc.trans hratio).trans_eq
  change (D*(R^c*R^(-mn)))/(R^(-c)*R^(-mp)) = D*R^(mp-mn+2*((d:ℝ)+1)*lam)
  rw [mul_div_assoc,← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp]
  congr 2
  dsimp [c]
  ring

end Falconer.Regularization

end OAI
