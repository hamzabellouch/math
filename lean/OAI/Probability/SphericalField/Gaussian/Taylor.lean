import Mathlib
import OAI.Probability.SphericalField.Control.Continuity

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma gaussian_abs_moment (v : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
      (Real.sqrt v)^n * ∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1 := by
  have hv : (⟨(Real.sqrt v)^2, sq_nonneg _⟩ : ℝ≥0) = v := by
    ext; exact Real.sq_sqrt v.coe_nonneg
  have hL := gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  simp only [mul_zero, NNReal.mk] at hL
  rw [hv, mul_one] at hL
  rw [← hL.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^n) (gaussianReal 0 v))]
  simp only [Function.comp_apply, id_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

lemma gaussian_law_integrable_abs_pow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) (n : ℕ) :
    Integrable (fun ω => |Z ω|^n) P := by
  have hm : MemLp id (n : ℝ≥0∞) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) (n : ℝ≥0))
  have hi : Integrable (fun x : ℝ => |x|^n) (Measure.map Z P) := by
    rw [hZ.map_eq]
    simpa only [Real.norm_eq_abs, id_eq] using hm.integrable_norm_pow'
  exact (integrable_map_measure hi.aestronglyMeasurable hZ.aemeasurable).mp hi

lemma gaussian_law_sq_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) :
    (∫ ω, (Z ω)^2 ∂P) = v := by
  have hi := hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2)
    (gaussianReal 0 v))
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  simp only [variance_id_gaussianReal, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    zero_pow (by decide : 2 ≠ 0), sub_zero] at hv
  exact hi.trans hv.symm

lemma bounded_real_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {Y : Ω → ℝ} (hY : AEMeasurable Y P)
    (C : ℝ) (hC : ∀ᵐ ω ∂P, |Y ω| ≤ C) : Integrable Y P := by
  exact (integrable_const C).mono' hY.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hC)

lemma boundedContinuousFunction_integrable_comp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (f : ℝ →ᵇ ℝ) {X : Ω → ℝ}
    (hX : AEMeasurable X P) : Integrable (fun ω => f (X ω)) P := by
  exact bounded_real_integrable (f.continuous.measurable.comp_aemeasurable hX) ‖f‖
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (X ω))

lemma gaussian_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₂ C₃ : ℝ) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) :
    |(∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  let d₁ := deriv (f : ℝ → ℝ)
  let d₂ := iteratedDeriv 2 (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hm₂ : Measurable d₂ := (hf.continuous_iteratedDeriv 2 (by norm_num)).measurable
  have hi₁ : Integrable (fun ω => d₁ (X ω) * Z ω) P := by
    have hz : Integrable Z P := by
      have hi := gaussian_law_integrable_abs_pow hZ 1
      exact (integrable_norm_iff hZ.aemeasurable.aestronglyMeasurable).mp (by
        simpa only [pow_one, Real.norm_eq_abs] using hi)
    apply hz.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have hi₂ : Integrable (fun ω => d₂ (X ω) * (Z ω)^2) P := by
    have hz : Integrable (fun ω => (Z ω)^2) P := by
      simpa only [sq_abs] using gaussian_law_integrable_abs_pow hZ 2
    apply hz.bdd_mul (hm₂.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, d₂] using h₂ (X ω)
  have hv₁ : (∫ ω, d₁ (X ω) * Z ω ∂P) = 0 := by
    have hh := (hI.comp hm₁ measurable_id).integral_fun_mul_eq_mul_integral
      (hm₁.comp_aemeasurable hX).aestronglyMeasurable hZ.aemeasurable.aestronglyMeasurable
    have hz : (∫ ω, Z ω ∂P) = 0 := hZ.integral_eq.trans (integral_id_gaussianReal)
    simpa only [Function.comp_apply, id_eq, hz, mul_zero] using hh
  have hv₂ : (∫ ω, d₂ (X ω) * (Z ω)^2 ∂P) = (v : ℝ) * (∫ ω, d₂ (X ω) ∂P) := by
    have hh := (hI.comp hm₂ (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      (hm₂.comp_aemeasurable hX).aestronglyMeasurable (hZ.aemeasurable.pow_const 2).aestronglyMeasurable
    simp only [Function.comp_apply, id_eq] at hh
    exact hh.trans (by rw [gaussian_law_sq_mean hZ, mul_comm])
  let R := fun ω => f (X ω + Z ω) - f (X ω) - d₁ (X ω) * Z ω - d₂ (X ω) * (Z ω)^2/2
  have hiR : Integrable R P :=
    (((boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)).sub
      (boundedContinuousFunction_integrable_comp f hX)).sub hi₁).sub (hi₂.div_const 2)
  have hR : ∀ ω, |R ω| ≤ C₃/6 * |Z ω|^3 := by
    intro ω
    have hh := second_order_taylor_bound hf C₃ h₃ (X ω) (X ω + Z ω)
    simpa only [add_sub_cancel_left, R, d₁, d₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hbound : |∫ ω, R ω ∂P| ≤ C₃/6 * ∫ ω, |Z ω|^3 ∂P := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, C₃/6 * |Z ω|^3 ∂P := integral_mono hiR.abs
        ((gaussian_law_integrable_abs_pow hZ 3).const_mul _) hR
      _ = _ := integral_const_mul _ _
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, d₂ (X ω) ∂P := by
    have ha := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
    have hb := boundedContinuousFunction_integrable_comp f hX
    have he₁ := integral_sub ((ha.sub hb).sub hi₁) (hi₂.div_const 2)
    have he₂ := integral_sub (ha.sub hb) hi₁
    have he₃ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂ he₃
    dsimp only [R]
    rw [he₁, he₂, he₃, integral_div, hv₁, hv₂]
    ring
  have hg : (∫ ω, |Z ω|^3 ∂P) = (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 :=
    (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^3) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 3)
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma drift_shift_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (C₁ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P)| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) := by
  let d₁ := deriv (f : ℝ → ℝ)
  have hm₁ : Measurable d₁ := (hf.continuous_deriv (by norm_num)).measurable
  have hiA := bounded_real_integrable hA K (Filter.Eventually.of_forall hAK)
  have hi₁ : Integrable (fun ω => d₁ (X ω) * A ω) P := by
    apply hiA.bdd_mul (hm₁.comp_aemeasurable hX).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, d₁] using h₁ (X ω)
  have ha := boundedContinuousFunction_integrable_comp f ((hX.add hZ.aemeasurable).add hA)
  have hb := boundedContinuousFunction_integrable_comp f (hX.add hZ.aemeasurable)
  let R := fun ω => f (X ω + Z ω + A ω) - f (X ω + Z ω) - d₁ (X ω) * A ω
  have hiR : Integrable R P := (ha.sub hb).sub hi₁
  have hR : ∀ ω, |R ω| ≤ (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) := by
    intro ω
    apply (drift_shift_taylor_bound hf C₂ h₂ (X ω) (Z ω) (A ω)).trans
    apply mul_le_mul_of_nonneg_left _ C₂.coe_nonneg
    have hsq : A ω ^2 ≤ (K : ℝ)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (A ω)) K.coe_nonneg).mpr (hAK ω)
    exact add_le_add (mul_le_mul_of_nonneg_left (hAK ω) (abs_nonneg _)) (by linarith)
  have hiz : Integrable (fun ω => |Z ω|) P := by
    simpa only [pow_one] using gaussian_law_integrable_abs_pow hZ 1
  have hbound : |∫ ω, R ω ∂P| ≤
      (C₂ : ℝ) * ((∫ ω, |Z ω| ∂P) * (K : ℝ) + (K : ℝ)^2/2) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C₂ : ℝ) * (|Z ω| * (K : ℝ) + (K : ℝ)^2/2) ∂P :=
        integral_mono hiR.abs (((hiz.mul_const K).add (integrable_const _)).const_mul C₂) hR
      _ = _ := by rw [integral_const_mul, integral_add (hiz.mul_const K) (integrable_const _), integral_mul_const]; simp
  have he : (∫ ω, R ω ∂P) = (∫ ω, f (X ω + Z ω + A ω) ∂P) -
      (∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, d₁ (X ω) * A ω ∂P) := by
    have he₁ := integral_sub (ha.sub hb) hi₁
    have he₂ := integral_sub ha hb
    simp only [Pi.add_apply, Pi.sub_apply] at he₁ he₂
    exact he₁.trans (by rw [he₂])
  have hg : (∫ ω, |Z ω| ∂P) = Real.sqrt v * ∫ x : ℝ, |x| ∂gaussianReal 0 1 := by
    have hh := (hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x|^1) (gaussianReal 0 v))).trans
      (gaussian_abs_moment v 1)
    simpa only [pow_one, Function.comp_apply] using hh
  rw [he, hg] at hbound
  exact hbound.trans_eq (by ring)

lemma gaussian_drift_taylor_mean_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : ℝ →ᵇ ℝ) (hf : ContDiff ℝ 3 (f : ℝ → ℝ))
    (C₁ C₃ : ℝ) (C₂ K : ℝ≥0) (h₁ : ∀ x, |deriv (f : ℝ → ℝ) x| ≤ C₁)
    (h₂ : ∀ x, |iteratedDeriv 2 (f : ℝ → ℝ) x| ≤ C₂)
    (h₃ : ∀ x, |iteratedDeriv 3 (f : ℝ → ℝ) x| ≤ C₃)
    {X Z A : Ω → ℝ} (hX : AEMeasurable X P) {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 v) P) (hI : IndepFun X Z P) (hA : AEMeasurable A P)
    (hAK : ∀ ω, |A ω| ≤ K) :
    |(∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P| ≤
      (C₂ : ℝ) * ((K : ℝ) * Real.sqrt v * (∫ x : ℝ, |x| ∂gaussianReal 0 1) + (K : ℝ)^2/2) +
      C₃/6 * (Real.sqrt v)^3 * ∫ x : ℝ, |x|^3 ∂gaussianReal 0 1 := by
  have hG := gaussian_taylor_mean_bound f hf C₁ C₂ C₃ h₁ h₂ h₃ hX hZ hI
  have hD := drift_shift_mean_bound f (hf.of_le (by norm_num)) C₁ C₂ K h₁ h₂ hX hZ hA hAK
  have hh := abs_add_le
    ((∫ ω, f (X ω + Z ω + A ω) ∂P) - (∫ ω, f (X ω + Z ω) ∂P) -
      (∫ ω, deriv (f : ℝ → ℝ) (X ω) * A ω ∂P))
    ((∫ ω, f (X ω + Z ω) ∂P) - (∫ ω, f (X ω) ∂P) -
      (v : ℝ)/2 * ∫ ω, iteratedDeriv 2 (f : ℝ → ℝ) (X ω) ∂P)
  convert hh.trans (add_le_add hD hG) using 1
  congr 1
  ring

end SphericalPerceptron
end
end

end OAI
