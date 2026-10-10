import OAI.Probability.InvariantIsing.Cavity.CavityLinearEnvelope
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianContinuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

namespace OAI

/-! A covariance bound gives a step-independent moment bound for the
remaining cavity tilt, including singular Gaussian covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityGaussianLinearMomentBound (d p : ℕ) (c M : ℝ) : ℝ :=
  Real.exp (2 * c) * ∫ z : EuclideanSpace ℝ (Fin d),
    Real.exp (((2 * p + 2 * c + 1) * Real.sqrt M) * ‖z‖) ∂stdGaussian _

lemma cavity_gaussian_linear_envelope {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) {M c : ℝ} (hSM : ‖S‖ ≤ M) (hc : 0 ≤ c) (p : ℕ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => cavityLinearMomentEnvelope p c ‖y‖)
      (multivariateGaussian 0 S) ∧
    (∫ y : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖y‖
      ∂multivariateGaussian 0 S) ≤ cavityGaussianLinearMomentBound d p c M := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  have hL : ‖L‖ ≤ Real.sqrt M := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, CFC.norm_sqrt S hS.nonneg]
    exact Real.sqrt_le_sqrt hSM
  have ha : 0 ≤ (2 : ℝ) * p + 2 * c + 1 := by positivity
  have hG := cavity_gaussian_linear_polynomial_exp_bound L (Real.sqrt_nonneg M) hL ha 0
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add] at hG
  have hi := hG.1.const_mul (Real.exp (2 * c))
  have he (z : EuclideanSpace ℝ (Fin d)) :
      cavityLinearMomentEnvelope p c ‖L z‖ =
        Real.exp (2 * c) * Real.exp ((2 * p + 2 * c + 1) * ‖L z‖) := Real.exp_add _ _
  have his : Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      cavityLinearMomentEnvelope p c ‖y‖) (multivariateGaussian 0 S) := by
    rw [multivariateGaussian, integrable_map_measure (by unfold cavityLinearMomentEnvelope; fun_prop) (by fun_prop)]
    simpa only [zero_add, Function.comp_def, cavityLinearMomentEnvelope, Real.exp_add, L] using hi
  refine ⟨his, ?_⟩
  rw [multivariateGaussian, integral_map (by fun_prop) (by unfold cavityLinearMomentEnvelope; fun_prop)]
  simp only [zero_add]
  change (∫ z : EuclideanSpace ℝ (Fin d), cavityLinearMomentEnvelope p c ‖L z‖ ∂stdGaussian _) ≤ _
  simp_rw [he]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hG.2 (Real.exp_pos _).le

theorem cavity_linear_tilt_gaussian_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (V : Ω × X → ℝ) (Y : X → EuclideanSpace ℝ (Fin d))
    (hV : Measurable V) (hY : Measurable Y)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (κ ∘ₘ P).map Y = multivariateGaussian 0 S)
    {M c : ℝ} (hSM : ‖S‖ ≤ M) (hc : 0 ≤ c) (p : ℕ)
    (hv : ∀ ω x, |V (ω, x)| ≤ c * (1 + ‖Y x‖)) :
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V (ω, x))) (κ ω) ∧
      Integrable (fun x => ‖Y x‖^p) ((κ ω).tilted (fun x => V (ω, x)))) ∧
    Integrable (fun ω => ∫ x, ‖Y x‖^p ∂(κ ω).tilted (fun x => V (ω, x))) P ∧
    (∫ ω, ∫ x, ‖Y x‖^p ∂(κ ω).tilted (fun x => V (ω, x)) ∂P) ≤
      cavityGaussianLinearMomentBound d p c M := by
  have hG := cavity_gaussian_linear_envelope S hS hSM hc p
  have hi : Integrable (fun x => cavityLinearMomentEnvelope p c ‖Y x‖) (κ ∘ₘ P) := by
    rw [← hLaw, integrable_map_measure (by unfold cavityLinearMomentEnvelope; fun_prop) hY.aemeasurable] at hG
    exact hG.1
  have h := cavity_linear_tilt_mean_moment P κ V (fun x => ‖Y x‖) hV hY.norm p hc
    (fun x => norm_nonneg _) hv hi
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  rw [← hLaw, integral_map hY.aemeasurable (by unfold cavityLinearMomentEnvelope; fun_prop)] at hG
  exact hG.2

end InvariantIsing

end

end OAI
