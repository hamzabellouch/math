import OAI.NumberTheory.DirichletL.LogarithmicControl
import OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmic
open HeckeFamily HeckeLogarithmicInput

def complexity (η : Character) (t : ℝ) : ℝ :=
  2*(η.modulus.absNorm : ℝ)*(3+|t|)^2

theorem complexity_ge_exp (η : Character) (t : ℝ) : Real.exp 1 ≤ complexity η t :=
  LogarithmicControl.conductor_height_scale_ge_exp _ t (modulus_norm_ge_one η)

theorem regular_disk_differentiable (η : Character) {a e t : ℝ}
    (ha : (1/2 : ℝ) ≤ a) (he : 0 < e) :
    DifferentiableOn ℂ (regular η) (ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) := by
  intro z hz
  exact (regular_differentiableAt η (by
    have hr := LogarithmicControl.disk_re_gt hz
    linarith)).differentiableWithinAt

theorem exists_uniform_polynomial_exponent :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ a e t : ℝ, 1/2 ≤ a → 0 < e → ∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-3*e),
        ‖regular η z‖ ≤ (complexity η t)^M := by
  obtain ⟨M, hM, hb⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := 2*uniformConstant) (p := 1) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro η hp a e t ha he z hz
  have hz2 : z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz
  have h := regular_disk_growth η hp a e t ha he.le hz2
  have hQ : (η.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ (η.modulus.absNorm : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (modulus_norm_ge_one η)
      (show (3/5 : ℝ)≤1 by norm_num)
  apply h.trans
  calc
    _ ≤ (4*uniformConstant)*(η.modulus.absNorm : ℝ)*(3+|t|)^2 := by
      gcongr
      exact mul_nonneg (by norm_num) uniformConstant_nonneg
    _ = (2*uniformConstant)*complexity η t := by unfold complexity; ring
    _ ≤ (complexity η t)^M := by simpa only [Real.rpow_one] using hb _ (complexity_ge_exp η t)

theorem disk_control_of_euler_log (e A ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ (a t : ℝ) (E : ℂ → ℂ),
      1/2 ≤ a → a ≤ 1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      DifferentiableOn ℂ E (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      EqOn (Complex.exp ∘ E) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨M,hM,hpoly⟩ := exists_uniform_polynomial_exponent
  obtain ⟨D,hD,hb⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, LogarithmicControl.outerConstant e A M/(2*e), hD, ?_, ?_⟩
  · have hB := LogarithmicControl.outerConstant_ge_one he he' hA hM
    positivity
  · intro η hp a t E ha ha' hzero hE hEL hEb
    exact hb a (complexity η t) (regular η) E ((2 : ℂ)+t*Complex.I) ha ha'
      (complexity_ge_exp η t) (regular_disk_differentiable η ha he) hzero
      (hpoly η hp a e t ha he) hE hEL hEb

end SevenEighths.HeckeLogarithmic

end

end OAI
