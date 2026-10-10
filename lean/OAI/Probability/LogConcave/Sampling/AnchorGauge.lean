import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.CircuitD

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable {d : ℕ}

def anchorGauge (C : ℝ) (z : Point d) : ℝ := 1+C+‖z‖

lemma anchorGauge_measurable (C : ℝ) : Measurable (anchorGauge (d:=d) C) := by
  unfold anchorGauge; fun_prop
lemma one_le_anchorGauge {C : ℝ} (hC : 0≤C) (z : Point d) : 1≤anchorGauge C z := by
  unfold anchorGauge; linarith [norm_nonneg z]
lemma anchorGauge_change (C : ℝ) (x y : Point d) :
    anchorGauge C y≤anchorGauge C x+dist x y := by
  have hh := norm_le_norm_add_norm_sub x y
  dsimp [anchorGauge]
  rw [dist_eq_norm]
  linarith
lemma anchorGauge_gaussian_integrable (C : ℝ) :
    Integrable (fun z : Point d => (anchorGauge C z)^2) (stdGaussian (Point d)) := by
  have h := (memLp_const (1+C) (p:=2) (μ:=stdGaussian (Point d))).add
    (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm
  exact h.integrable_sq
lemma anchorGauge_gaussian_moment (C : ℝ) :
    (∫z : Point d,(anchorGauge C z)^2 ∂stdGaussian (Point d))≤2*(1+C)^2+2*d := by
  have hi2 : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.integrable_sq
  have hi : Integrable (fun z : Point d => 2*(1+C)^2+2*‖z‖^2) (stdGaussian (Point d)) :=
    (integrable_const _).add (hi2.const_mul _)
  apply (integral_mono (anchorGauge_gaussian_integrable C) hi (fun z => ?_)).trans_eq
    (show (∫z : Point d,2*(1+C)^2+2*‖z‖^2 ∂stdGaussian (Point d))=2*(1+C)^2+2*d by
      rw [integral_add (integrable_const _) (hi2.const_mul _),
        integral_const,probReal_univ,one_smul,integral_const_mul,stdGaussian_sq_norm])
  dsimp [anchorGauge]
  nlinarith [sq_nonneg (1+C-‖z‖)]
lemma anchorGauge_circuitD_moment (hd : 1≤d) (F : Point d → ℝ) (x : Point d) :
    (∫z : Point d,(anchorGauge (circuitD F x) z)^2 ∂stdGaussian (Point d))≤10*(circuitD F x)^2 := by
  apply (anchorGauge_gaussian_moment _).trans
  have hs := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ)≤d)
  have hdim : (1:ℝ)≤d := by exact_mod_cast hd
  have hD := sqrt_le_circuitD F x
  have h0 := circuitD_nonneg F x
  have hr0 := Real.sqrt_nonneg (d:ℝ)
  have hr1 : 1≤Real.sqrt (d:ℝ) := by nlinarith
  have h1 : 1≤circuitD F x := hr1.trans hD
  have hsq := pow_le_pow_left₀ hr0 hD 2
  nlinarith [sq_nonneg (circuitD F x-1)]
end LogConcaveSampling

end

end

end OAI
