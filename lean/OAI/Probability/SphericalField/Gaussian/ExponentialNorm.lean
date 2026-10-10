import Mathlib

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace SphericalPerceptron

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

lemma gaussian_integrable_exp_norm (a : ℝ) : Integrable (fun y : E => Real.exp (a*‖y‖)) μ := by
  obtain ⟨c,hc,hI⟩ := IsGaussian.exists_integrable_exp_sq μ
  have hh (y : E) : a*‖y‖ ≤ c*‖y‖^2+a^2/(4*c) := by
    have h := sq_nonneg (2*c*‖y‖-a)
    have hd : a^2/(4*c)*(4*c)=a^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  apply (hI.const_mul (Real.exp (a^2/(4*c)))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hh y]

lemma gaussian_integrable_norm_sq_exp (a : ℝ) :
    Integrable (fun y : E => ‖y‖^2*Real.exp (a*‖y‖)) μ := by
  have he : integrableExpSet (fun y : E => ‖y‖) μ=univ :=
    Set.eq_univ_of_forall (gaussian_integrable_exp_norm μ)
  have ht : a ∈ interior (integrableExpSet (fun y : E => ‖y‖) μ) := by simp [he]
  have h := integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht 2
  simpa using h

lemma gaussian_integrable_exp_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a σ : ℝ) (x : E) :
    Integrable (fun y : E => Real.exp (a*f (x+σ • y))) μ := by
  have hbound (y : E) : a*f (x+σ • y) ≤ |a| *|f x|+(|a| *L*|σ|)*‖y‖ := by
    have hl := hf.dist_le_mul (x+σ • y) x
    simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at hl
    have hn := abs_add_le (f (x+σ • y)-f x) (f x)
    rw [sub_add_cancel] at hn
    have hmul := mul_le_mul_of_nonneg_left (le_trans hn (add_le_add hl le_rfl)) (abs_nonneg a)
    have hle := le_abs_self (a*f (x+σ • y))
    rw [abs_mul] at hle
    nlinarith
  have hfc := hf.continuous
  apply ((gaussian_integrable_exp_norm μ (|a| *L*|σ|)).const_mul
    (Real.exp (|a| *|f x|))).mono' (by fun_prop)
  exact ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    exact Real.exp_le_exp.mpr (hbound y)

lemma gaussian_integrable_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (σ : ℝ) (x : E) :
    Integrable (fun y : E => f (x+σ • y)) μ := by
  have he : integrableExpSet (fun y : E => f (x+σ • y)) μ=univ :=
    Set.eq_univ_of_forall (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)
  have ht : (0:ℝ) ∈ interior (integrableExpSet (fun y : E => f (x+σ • y)) μ) := by simp [he]
  exact (memLp_of_mem_interior_integrableExpSet ht (1:ℝ≥0)).integrable (by simp)

end
end SphericalPerceptron
end
end

end OAI
