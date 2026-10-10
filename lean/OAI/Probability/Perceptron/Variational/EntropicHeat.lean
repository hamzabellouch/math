import Mathlib
import OAI.Probability.Perceptron.Variational.EntropicParameter

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

lemma integrable_of_all_exp (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) :
    Integrable X μ :=
  (memLp_of_mem_interior_integrableExpSet (mem_interior_integrableExpSet_of_all μ hX 0) 1).integrable (by simp)

omit [IsProbabilityMeasure μ] in
lemma all_exp_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ) (c : ℝ) :
    ∀ t : ℝ, Integrable (fun ω => Real.exp (t*(X ω+c))) μ := by
  intro t
  simpa only [mul_add,Real.exp_add] using (hX t).mul_const (Real.exp (t*c))

lemma entropicMean_add_const (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (p c : ℝ) : entropicMean μ p (fun ω => X ω+c)=entropicMean μ p X+c := by
  by_cases hp : p=0
  · subst p
    rw [entropicMean_zero μ (all_exp_add_const μ hX c),entropicMean_zero μ hX,
      integral_add (integrable_of_all_exp μ hX) (integrable_const c),integral_const]
    simp
  · rw [entropicMean_eq_div μ (all_exp_add_const μ hX c) hp,entropicMean_eq_div μ hX hp]
    simp only [cgf,mgf_add_const]
    rw [Real.log_mul (ne_of_gt (mgf_pos (hX p))) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
    field_simp

lemma entropicMean_mono_variable
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    (hXY : X ≤ᵐ[μ] Y) {p : ℝ} (hp : 0 ≤ p) :
    entropicMean μ p X ≤ entropicMean μ p Y := by
  rcases hp.eq_or_lt with hp|hp
  · subst p
    rw [entropicMean_zero μ hX,entropicMean_zero μ hY]
    exact integral_mono_ae (integrable_of_all_exp μ hX) (integrable_of_all_exp μ hY) hXY
  · rw [entropicMean_eq_div μ hX (ne_of_gt hp),entropicMean_eq_div μ hY (ne_of_gt hp)]
    apply div_le_div_of_nonneg_right _ hp.le
    exact Real.log_le_log (mgf_pos (hX p)) (mgf_mono_of_nonneg hXY hp.le (hY p))

lemma entropicMean_bounded_difference
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t*Y ω)) μ)
    {C p : ℝ} (hp : 0 ≤ p) (hXY : ∀ᵐ ω ∂μ, |X ω-Y ω| ≤ C) :
    |entropicMean μ p X-entropicMean μ p Y| ≤ C := by
  have h1 : X ≤ᵐ[μ] (fun ω => Y ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).2
    linarith
  have h2 : Y ≤ᵐ[μ] (fun ω => X ω+C) := by
    filter_upwards [hXY] with ω hω
    have := (abs_le.mp hω).1
    linarith
  have H1 := entropicMean_mono_variable μ hX (all_exp_add_const μ hY C) h1 hp
  have H2 := entropicMean_mono_variable μ hY (all_exp_add_const μ hX C) h2 hp
  rw [entropicMean_add_const μ hY] at H1
  rw [entropicMean_add_const μ hX] at H2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

def gaussianEntropic (p σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  entropicMean μ p (fun y => f (x+σ • y))

lemma gaussianEntropic_lipschitz {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p σ : ℝ} (hp : 0 ≤ p) :
    LipschitzWith L (gaussianEntropic μ p σ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,gaussianEntropic]
  apply entropicMean_bounded_difference μ
    (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)
    (fun a => gaussian_integrable_exp_lipschitz μ hf a σ y) hp
  exact ae_of_all _ fun z => by
    simpa only [Real.dist_eq,dist_add_right] using hf.dist_le_mul (x+σ • z) (y+σ • z)

lemma gaussianEntropic_mono_parameter {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (σ : ℝ) (x : E) :
    Monotone (fun p => gaussianEntropic μ p σ f x) :=
  entropicMean_monotone μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)

lemma gaussianEntropic_zero {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (σ : ℝ) (x : E) :
    gaussianEntropic μ 0 σ f x=∫ y, f (x+σ • y) ∂μ :=
  entropicMean_zero μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)

lemma gaussianEntropic_pos {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p : ℝ} (hp : p ≠ 0) (σ : ℝ) (x : E) :
    gaussianEntropic μ p σ f x=Real.log (∫ y, Real.exp (p*f (x+σ • y)) ∂μ)/p :=
  entropicMean_eq_div μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) hp

lemma gaussianEntropic_mono {f g : E → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g) {p : ℝ} (hp : 0 ≤ p)
    (σ : ℝ) (hfg : ∀ x, f x ≤ g x) (x : E) :
    gaussianEntropic μ p σ f x ≤ gaussianEntropic μ p σ g x :=
  entropicMean_mono_variable μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x)
    (fun a => gaussian_integrable_exp_lipschitz μ hg a σ x)
    (ae_of_all _ fun noise => hfg (x+σ • noise)) hp

lemma gaussianEntropic_add_const {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (p σ c : ℝ) (x : E) :
    gaussianEntropic μ p σ (fun z => f z+c) x=gaussianEntropic μ p σ f x+c :=
  entropicMean_add_const μ (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) p c

def gaussianEntropicParamConstant (L S : ℝ) : ℝ :=
  L^2*(∫ y : E, ‖y‖^2*Real.exp (L*S*‖y‖) ∂μ) /
    mgf (fun y : E => ‖y‖) μ (-(L*S))

lemma gaussianEntropicParamConstant_nonneg (L S : ℝ) :
    0 ≤ gaussianEntropicParamConstant μ L S := by
  apply div_nonneg
  · exact mul_nonneg (sq_nonneg _) (integral_nonneg fun y =>
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  · exact (mgf_pos (gaussian_integrable_exp_norm μ (-(L*S)))).le

lemma gaussianEntropic_parameter_bound {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {p q σ S : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1)
    (hσ : 0 ≤ σ) (hσS : σ ≤ S) (x : E) :
    |gaussianEntropic μ p σ f x-gaussianEntropic μ q σ f x| ≤
      gaussianEntropicParamConstant μ L S*σ^2*|p-q| := by
  let X : E → ℝ := fun y => f (x+σ • y)-f x
  have hX : ∀ t : ℝ, Integrable (fun y => Real.exp (t*X y)) μ := by
    intro t
    simpa [X,sub_eq_add_neg] using all_exp_add_const μ
      (fun a => gaussian_integrable_exp_lipschitz μ hf a σ x) (-f x) t
  have hnorm (y : E) : |X y| ≤ (L:ℝ)*σ*‖y‖ := by
    have hh := hf.dist_le_mul (x+σ • y) x
    simpa only [X,Real.dist_eq,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg hσ,mul_assoc] using hh
  have hlin (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (y : E) :
      |t*X y| ≤ (L:ℝ)*S*‖y‖ := by
    rw [abs_mul,abs_of_nonneg ht.1]
    calc
      t*|X y| ≤ |X y| := mul_le_of_le_one_left (abs_nonneg _) ht.2
      _ ≤ (L:ℝ)*σ*‖y‖ := hnorm y
      _ ≤ (L:ℝ)*S*‖y‖ := by gcongr
  let c := mgf (fun y : E => ‖y‖) μ (-((L:ℝ)*S))
  have hc : 0 < c := mgf_pos (gaussian_integrable_exp_norm μ (-((L:ℝ)*S)))
  let I := ∫ y : E, ‖y‖^2*Real.exp ((L:ℝ)*S*‖y‖) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      deriv (deriv (cgf X μ)) t ≤ gaussianEntropicParamConstant μ L S*σ^2 := by
    have hl : c ≤ mgf X μ t := by
      apply integral_mono (gaussian_integrable_exp_norm μ (-((L:ℝ)*S))) (hX t)
      intro y
      apply Real.exp_le_exp.mpr
      have hh := (abs_le.mp (hlin t ht y)).1
      nlinarith
    have hu : (∫ y, (X y)^2*Real.exp (t*X y) ∂μ) ≤ (L:ℝ)^2*σ^2*I := by
      have hi := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
        (mem_interior_integrableExpSet_of_all μ hX t) 2
      calc
        _ ≤ ∫ y : E, ((L:ℝ)^2*σ^2)*(‖y‖^2*Real.exp ((L:ℝ)*S*‖y‖)) ∂μ := by
          apply integral_mono hi ((gaussian_integrable_norm_sq_exp μ ((L:ℝ)*S)).const_mul _)
          intro y
          have hs : (X y)^2 ≤ (L:ℝ)^2*σ^2*‖y‖^2 := by
            have hn := hnorm y
            have hz : 0 ≤ (L:ℝ)*σ*‖y‖ := by positivity
            simpa only [sq_abs,mul_pow] using (sq_le_sq₀ (abs_nonneg (X y)) hz).mpr hn
          have he : Real.exp (t*X y) ≤ Real.exp ((L:ℝ)*S*‖y‖) :=
            Real.exp_le_exp.mpr ((le_abs_self _).trans (hlin t ht y))
          have hh := mul_le_mul hs he (Real.exp_pos _).le (by positivity)
          convert hh using 1; ring
        _ = _ := by rw [integral_const_mul]
    have hh := cgf_second_le_of_moments μ hX hc (by positivity) hl hu
    convert hh using 1; dsimp [gaussianEntropicParamConstant,c,I]; ring
  have H := entropicMean_param_bound μ hX
    (mul_nonneg (gaussianEntropicParamConstant_nonneg μ L S) (sq_nonneg σ)) hbound hp hq
  have he (a : ℝ) : entropicMean μ a X=gaussianEntropic μ a σ f x-f x := by
    simpa [X,gaussianEntropic,sub_eq_add_neg] using entropicMean_add_const μ
      (fun b => gaussian_integrable_exp_lipschitz μ hf b σ x) a (-f x)
  rw [he p,he q] at H
  convert H using 1; congr 1; ring

end SphericalPerceptronFreeEnergy
end

end OAI
