import Mathlib
import OAI.Probability.Perceptron.Cascade.DecoratedWeightedTotal

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma normalizedMeasure_prod {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [SFinite ν] [SFinite ρ]
    (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ⊤) :
    normalizedMeasure (ν.prod ρ) = (normalizedMeasure ν).prod (normalizedMeasure ρ) := by
  unfold normalizedMeasure
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  congr 1
  rw [← univ_prod_univ,Measure.prod_prod,ENNReal.mul_inv (Or.inl hν0) (Or.inl hνf)]

lemma exponentialMarkTilt_prod_add {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (b : ℝ) {f : S → ℝ} {g : T → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hIf : Integrable (fun s => Real.exp (b*f s)) ν) :
    exponentialMarkTilt (ν.prod ρ) b (fun p => f p.1+g p.2) =
      (exponentialMarkTilt ν b f).prod (exponentialMarkTilt ρ b g) := by
  have hνmass : (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*f s)))) univ =
      ENNReal.ofReal (∫ s, Real.exp (b*f s) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hIf (ae_of_all _ fun s => (Real.exp_pos _).le)).symm
  have hd : (fun p : S×T => ENNReal.ofReal (Real.exp (b*(f p.1+g p.2)))) =
      (fun p : S×T => ENNReal.ofReal (Real.exp (b*f p.1))* ENNReal.ofReal (Real.exp (b*g p.2))) := by
    funext p
    rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold exponentialMarkTilt
  rw [hd,← prod_withDensity ((hf.const_mul b).exp.ennreal_ofReal) ((hg.const_mul b).exp.ennreal_ofReal)]
  apply normalizedMeasure_prod
  · rw [hνmass]; exact ENNReal.ofReal_ne_zero_iff.mpr (integral_exp_pos hIf)
  · rw [hνmass]; exact ENNReal.ofReal_ne_top

lemma fractional_log_moment_prod_add {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (b : ℝ) {f : S → ℝ} {g : T → ℝ}
    (hIf : Integrable (fun s => Real.exp (b*f s)) ν)
    (hIg : Integrable (fun t => Real.exp (b*g t)) ρ) :
    Real.log (∫ p, Real.exp (b*(f p.1+g p.2)) ∂ν.prod ρ)/b =
      Real.log (∫ s, Real.exp (b*f s) ∂ν)/b + Real.log (∫ t, Real.exp (b*g t) ∂ρ)/b := by
  simp_rw [mul_add,Real.exp_add]
  rw [integral_prod_mul (fun s => Real.exp (b*f s)) (fun t => Real.exp (b*g t)),Real.log_mul (integral_exp_pos hIf).ne' (integral_exp_pos hIg).ne',add_div]

def productMarkLaw {S T : Type} [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) : ProbabilityMeasure (S×T) :=
  ⟨(ν : Measure S).prod (ρ : Measure T),inferInstance⟩

theorem finiteCascadeLogRecursion_add_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    {H : X → ℝ} {G : Y → ℝ}
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) :
    finiteCascadeLogRecursion (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
        (fun q => H q.1+G q.2) (x,y) =
      finiteCascadeLogRecursion ν step₁ n z H x + finiteCascadeLogRecursion ρ step₂ n z G y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    rcases hIH with ⟨hHroot,hHtail⟩
    rcases hIG with ⟨hGroot,hGtail⟩
    conv_lhs => rw [finiteCascadeLogRecursion]
    change Real.log (∫ p : S×T, Real.exp (z 0 *
      finiteCascadeLogRecursion (productMarkLaw ν ρ)
        (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n (fun i => z i.succ)
          (fun q => H q.1+G q.2) (step₁ (x,p.1),step₂ (y,p.2))) ∂(ν : Measure S).prod (ρ : Measure T))/(z 0) = _
    simp_rw [ih (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail]
    exact fractional_log_moment_prod_add (ν : Measure S) (ρ : Measure T) (z 0) (hHroot x) (hGroot y)

lemma real_quadratic_complete_square {b : ℝ} (hb : b ≠ 0) (c d y : ℝ) :
    Real.exp (-b*y^2+c*y+d) =
      Real.exp (d+c^2/(4*b))*Real.exp (-b*(y-c/(2*b))^2) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

lemma real_quadratic_integrable {b : ℝ} (hb : 0 < b) (c d : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-b*y^2+c*y+d)) := by
  simp_rw [real_quadratic_complete_square hb.ne']
  exact ((integrable_exp_neg_mul_sq hb).comp_sub_right (c/(2*b))).const_mul _

lemma real_quadratic_integral {b : ℝ} (hb : 0 < b) (c d : ℝ) :
    (∫ y : ℝ, Real.exp (-b*y^2+c*y+d)) =
      Real.exp (d+c^2/(4*b))*Real.sqrt (Real.pi/b) := by
  simp_rw [real_quadratic_complete_square hb.ne']
  rw [integral_const_mul, integral_sub_right_eq_self (fun y : ℝ => Real.exp (-b*y^2)),integral_gaussian]

lemma standardGaussian_quadratic_density (a c d y : ℝ) :
    gaussianPDFReal 0 1 y * Real.exp (a*y^2+c*y+d) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-a)*y^2+c*y+d) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma standardGaussian_quadratic_integrable {a : ℝ} (ha : a < 1/2) (c d : ℝ) :
    Integrable (fun y : ℝ => Real.exp (a*y^2+c*y+d)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [smul_eq_mul]
  have he : (fun y : ℝ => (gaussianPDF 0 1 y).toReal * Real.exp (a*y^2+c*y+d)) =
      (fun y : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-a)*y^2+c*y+d)) := by
    funext y
    rw [toReal_gaussianPDF]
    exact standardGaussian_quadratic_density a c d y
  rw [he]
  exact (real_quadratic_integrable (by linarith : 0 < 1/2-a) c d).const_mul _

lemma standardGaussian_quadratic_integral {a : ℝ} (ha : a < 1/2) (c d : ℝ) :
    (∫ y, Real.exp (a*y^2+c*y+d) ∂gaussianReal 0 1) =
      Real.exp (d+c^2/(4*(1/2-a))) / Real.sqrt (1-2*a) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul,standardGaussian_quadratic_density]
  rw [integral_const_mul,real_quadratic_integral (by linarith : 0 < 1/2-a)]
  have hratio : Real.sqrt (Real.pi/(1/2-a)) = Real.sqrt (2*Real.pi)/Real.sqrt (1-2*a) := by
    rw [←Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  rw [hratio]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2*Real.pi))]

lemma gaussian_quadratic_fractional_integrable {b z σ : ℝ} (hb : 0 < b)
    (ha : 0 < b-z*σ^2) (c x : ℝ) :
    Integrable (fun y : ℝ => Real.exp (z*(c+(x+σ*y)^2/(2*b)))) (gaussianReal 0 1) := by
  have hhalf : z*σ^2/(2*b) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
    linarith
  convert standardGaussian_quadratic_integrable hhalf (z*x*σ/b) (z*c+z*x^2/(2*b)) using 1
  funext y
  congr 1
  field_simp
  ring

lemma gaussian_quadratic_fractional_log {b z σ : ℝ} (hb : 0 < b) (hz : z ≠ 0)
    (ha : 0 < b-z*σ^2) (c x : ℝ) :
    Real.log (∫ y, Real.exp (z*(c+(x+σ*y)^2/(2*b))) ∂gaussianReal 0 1)/z =
      c+(Real.log b-Real.log (b-z*σ^2))/(2*z)+x^2/(2*(b-z*σ^2)) := by
  have hhalf : z*σ^2/(2*b) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
    linarith
  have hfun : (fun y : ℝ => Real.exp (z*(c+(x+σ*y)^2/(2*b)))) =
      (fun y : ℝ => Real.exp ((z*σ^2/(2*b))*y^2+(z*x*σ/b)*y+(z*c+z*x^2/(2*b)))) := by
    funext y
    congr 1
    field_simp
    ring
  have hprec : 1-2*(z*σ^2/(2*b)) = (b-z*σ^2)/b := by field_simp
  have hprec' : 1/2-z*σ^2/(2*b) = (b-z*σ^2)/(2*b) := by field_simp
  rw [hfun,standardGaussian_quadratic_integral hhalf,hprec,
    Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr (div_pos ha hb)).ne',
    Real.log_exp, Real.log_sqrt (div_pos ha hb).le,Real.log_div ha.ne' hb.ne',hprec']
  field_simp [hb.ne',hz,ha.ne']
  ring

def gaussianShiftStep (σ : ℕ → ℝ) (p : (ℕ → ℝ) × ℝ) : ℕ → ℝ :=
  fun i => p.1 (i+1)+σ i*p.2

lemma gaussianShiftStep_measurable (σ : ℕ → ℝ) : Measurable (gaussianShiftStep σ) := by
  unfold gaussianShiftStep
  fun_prop

def standardGaussianMark : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1,inferInstance⟩

def quadraticCascadePrecision (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => b
  | n+1, z => quadraticCascadePrecision σ b n (fun i => z i.succ)-z 0*(σ n)^2

def quadraticCascadeOffset (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeOffset σ b n (fun i => z i.succ)+
      (Real.log (quadraticCascadePrecision σ b n (fun i => z i.succ))-
        Real.log (quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

lemma quadraticCascadePrecision_tail_pos (σ : ℕ → ℝ) (b : ℝ) (n : ℕ) (z : Fin (n+1) → ℝ)
    (hz : 0 ≤ z 0) (hp : 0 < quadraticCascadePrecision σ b (n+1) z) :
    0 < quadraticCascadePrecision σ b n (fun i => z i.succ) := by
  have hsq := mul_nonneg hz (sq_nonneg (σ n))
  dsimp [quadraticCascadePrecision] at hp
  linarith

theorem finiteCascade_quadratic_recursion (σ : ℕ → ℝ) (b c : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x : ℕ → ℝ, finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep σ) n z
      (fun x => c+(x 0)^2/(2*b)) x =
      c+quadraticCascadeOffset σ b n z+(x n)^2/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable standardGaussianMark (gaussianShiftStep σ)
      (fun x => c+(x 0)^2/(2*b)) n z := by
  induction n with
  | zero => exact ⟨fun _ => by simp [finiteCascadeLogRecursion,quadraticCascadeOffset,quadraticCascadePrecision],trivial⟩
  | succ n ih =>
    have hpt := quadraticCascadePrecision_tail_pos σ b n z (hz 0).le hp
    obtain ⟨heq,hint⟩ := ih (fun i => z i.succ) (fun i => hz i.succ) hpt
    constructor
    · intro x
      conv_lhs => rw [finiteCascadeLogRecursion]
      unfold fractionalLogMoment
      simp_rw [heq]
      change Real.log (∫ y, Real.exp (z 0 *
        (c+quadraticCascadeOffset σ b n (fun i => z i.succ)+
          (x (n+1)+σ n*y)^2/(2*quadraticCascadePrecision σ b n (fun i => z i.succ))))
          ∂gaussianReal 0 1)/(z 0) = _
      rw [gaussian_quadratic_fractional_log hpt (hz 0).ne' hp]
      dsimp [quadraticCascadeOffset,quadraticCascadePrecision]
      ring
    · refine ⟨?_,hint⟩
      intro x
      simp_rw [heq]
      exact gaussian_quadratic_fractional_integrable hpt hp
        (c+quadraticCascadeOffset σ b n (fun i => z i.succ)) (x (n+1))

theorem canonical_cascade_quadratic_log (σ : ℕ → ℝ) (b c : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (x : ℕ → ℝ) :
    (∫ η, Real.log (decoratedTerminalTotal (gaussianShiftStep σ) (fun x => c+(x 0)^2/(2*b)) n (x,η) /
      decoratedTerminalTotal (gaussianShiftStep σ) (fun _ => 0) n (x,η))
        ∂decoratedCascadeLaw standardGaussianMark n z) =
      c+quadraticCascadeOffset σ b n z+(x n)^2/(2*quadraticCascadePrecision σ b n z) := by
  have hq := finiteCascade_quadratic_recursion σ b c n z hz0 hp
  rw [finiteCascade_terminal_log_recursion_of_fractional standardGaussianMark (gaussianShiftStep σ)
    (gaussianShiftStep_measurable σ) n z hz hz0 hz1 (by fun_prop) hq.2]
  exact hq.1 x

lemma canonical_scalar_integrable {b : ℝ} (hb : 0 < b) (u : ℝ) :
    Integrable (fun y : ℝ => Real.exp ((1-b)*y^2/2+u*y)) (gaussianReal 0 1) := by
  convert standardGaussian_quadratic_integrable (a := (1-b)/2) (by linarith) u 0 using 1
  funext y
  congr 1
  ring

lemma canonical_scalar_integral {b : ℝ} (hb : 0 < b) (u : ℝ) :
    (∫ y, Real.exp ((1-b)*y^2/2+u*y) ∂gaussianReal 0 1) =
      Real.exp (u^2/(2*b))/Real.sqrt b := by
  have he : (fun y : ℝ => Real.exp ((1-b)*y^2/2+u*y)) =
      (fun y : ℝ => Real.exp (((1-b)/2)*y^2+u*y+0)) := by funext y; congr 1; ring
  rw [he,standardGaussian_quadratic_integral (by linarith : (1-b)/2 < 1/2)]
  congr 2 <;> ring

lemma canonical_scalar_log {b : ℝ} (hb : 0 < b) (u : ℝ) :
    Real.log (∫ y, Real.exp ((1-b)*y^2/2+u*y) ∂gaussianReal 0 1) =
      -Real.log b/2+u^2/(2*b) := by
  rw [canonical_scalar_integral hb,Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr hb).ne',
    Real.log_exp,Real.log_sqrt hb.le]
  ring

lemma quadraticCascadePrecision_le (σ : ℕ → ℝ) (b : ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) : quadraticCascadePrecision σ b n z ≤ b := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have ht := ih (fun i => z i.succ) (fun i => hz i.succ)
    have hq := mul_nonneg (hz 0) (sq_nonneg (σ n))
    dsimp [quadraticCascadePrecision]
    linarith

lemma quadraticCascadePrecision_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ) (b : ℝ) :
    HasDerivAt (fun b => quadraticCascadePrecision σ b n z) 1 b := by
  induction n with
  | zero => exact hasDerivAt_id b
  | succ n ih => exact (ih (fun i => z i.succ)).sub_const _

def quadraticCascadeReciprocalSlope (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeReciprocalSlope σ b n (fun i => z i.succ)+
      (1/(quadraticCascadePrecision σ b n (fun i => z i.succ))-
        1/(quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

lemma quadraticCascadeOffset_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) {b : ℝ} (hp : 0 < quadraticCascadePrecision σ b n z) :
    HasDerivAt (fun b => quadraticCascadeOffset σ b n z)
      (quadraticCascadeReciprocalSlope σ b n z) b := by
  induction n with
  | zero => exact hasDerivAt_const b 0
  | succ n ih =>
    have hpt := quadraticCascadePrecision_tail_pos σ b n z (hz 0) hp
    exact (ih (fun i => z i.succ) (fun i => hz i.succ) hpt).add
      ((((quadraticCascadePrecision_hasDerivAt σ n (fun i => z i.succ) b).log hpt.ne').sub
        ((quadraticCascadePrecision_hasDerivAt σ (n+1) z b).log hp.ne')).div_const (2*z 0))

def canonicalGaussianFreeValue (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ) (r b : ℝ) : ℝ :=
  -Real.log b/2 + quadraticCascadeOffset σ b n z+r/(2*quadraticCascadePrecision σ b n z)

lemma canonicalGaussianFreeValue_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (r : ℝ) {b : ℝ} (hp : 0 < quadraticCascadePrecision σ b n z) :
    HasDerivAt (canonicalGaussianFreeValue σ n z r)
      (-1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-r/(2*(quadraticCascadePrecision σ b n z)^2)) b := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b n z hz)
  have hq := quadraticCascadePrecision_hasDerivAt σ n z b
  have ht := (((Real.hasDerivAt_log hb.ne').neg.div_const 2).add
    (quadraticCascadeOffset_hasDerivAt σ n z hz hp)).add
      ((hasDerivAt_const b r).div (hq.const_mul 2) (by positivity))
  have hd : -b⁻¹/2+quadraticCascadeReciprocalSlope σ b n z+
      (0*(2*quadraticCascadePrecision σ b n z)-r*(2*1))/(2*quadraticCascadePrecision σ b n z)^2 =
      -1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-r/(2*(quadraticCascadePrecision σ b n z)^2) := by
    field_simp [hb.ne',hp.ne']
    ring
  exact ht.congr_deriv hd

def cascadeLogFluctuationConstant (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  4*∫ η, (Real.log (cascadeTotal n η))^2 ∂cascadeLaw n z

lemma cascadeLogFluctuationConstant_nonneg (n : ℕ) (z : Fin n → ℝ) :
    0 ≤ cascadeLogFluctuationConstant n z :=
  mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _)

lemma decoratedCascade_log_second_moment_bound {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ) :
    MemLp (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) 2
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ∧
    (∫ η, (Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))-c)^2 ∂decoratedCascadeLaw ν n z) ≤
        cascadeLogFluctuationConstant n z := by
  have hid := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 F hF hI hM x
  have hiz := decoratedWeightedTotal_identDistrib ν step hstep n z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  have hld := hid.comp Real.measurable_log
  have hlz := hiz.comp Real.measurable_log
  have hL := cascadeTotal_log_memLp_two n z hz hz0 hz1
  have hmD := hld.memLp_iff.mpr hL
  have hmZ := hlz.memLp_iff.mpr hL
  have hp := (cascadeTotal_regular n z hz hz0 hz1).1
  have hdpos := hid.symm.ae_snd measurableSet_Ioi hp
  have hzpos := hiz.symm.ae_snd measurableSet_Ioi hp
  have he : (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) =ᵐ[(decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))]
      (fun η => c+Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η))) := by
    filter_upwards [hdpos,hzpos] with η hη hg
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hη.ne') hg.ne',
      Real.log_mul (Real.exp_ne_zero _) hη.ne',Real.log_exp]
  refine ⟨(memLp_congr_ae he).mpr (((memLp_const c).add hmD).sub hmZ),?_⟩
  have heD := (hld.comp (by fun_prop : Measurable (fun t : ℝ => t^2))).integral_eq
  have heZ := (hlz.comp (by fun_prop : Measurable (fun t : ℝ => t^2))).integral_eq
  simp only [Function.comp_apply] at heD heZ
  calc
    _ = ∫ η, (Real.log (decoratedWeightedTotal step n F (x,η))-
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))^2 ∂decoratedCascadeLaw ν n z := by
      apply integral_congr_ae
      filter_upwards [he] with η hη
      rw [hη]
      ring
    _ ≤ ∫ η, (2*(Real.log (decoratedWeightedTotal step n F (x,η)))^2+
        2*(Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))^2) ∂decoratedCascadeLaw ν n z := by
      apply integral_mono (hmD.sub hmZ).integrable_sq
        ((hmD.integrable_sq.const_mul 2).add (hmZ.integrable_sq.const_mul 2))
      intro η
      dsimp only [Function.comp_apply,Pi.sub_apply,Pi.add_apply]
      nlinarith [sq_nonneg (Real.log (decoratedWeightedTotal step n F (x,η))+
        Real.log (decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))]
    _ = _ := by
      have hsplit := integral_add (hmD.integrable_sq.const_mul 2) (hmZ.integrable_sq.const_mul 2)
      simp only [Function.comp_apply] at hsplit
      rw [hsplit,integral_const_mul,integral_const_mul,heD,heZ]
      unfold cascadeLogFluctuationConstant
      ring

lemma decoratedCascade_log_deviation_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))
      {η | ε ≤ |Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
        decoratedWeightedTotal step n (fun _ _ => 0) (x,η))-c|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  obtain ⟨hm,hbound⟩ := decoratedCascade_log_second_moment_bound ν step hstep n z hz hz0 hz1 F hF hI hM x c
  have he := decoratedCascade_log_identity ν step hstep n z hz hz0 hz1 F hF hI hM x c
  have hvar : variance (fun η => Real.log (Real.exp c*decoratedWeightedTotal step n F (x,η) /
      decoratedWeightedTotal step n (fun _ _ => 0) (x,η)))
        (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) ≤ cascadeLogFluctuationConstant n z := by
    rw [variance_eq_integral hm.aemeasurable,he]
    exact hbound
  have hc := meas_ge_le_variance_div_sq hm hε
  rw [he] at hc
  exact hc.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg ε)))

lemma finiteCascade_terminal_log_deviation_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    {H : X → ℝ} (hH : Measurable H) (hI : finiteCascadeFractionalIntegrable ν step H n z) (x : X)
    {ε : ℝ} (hε : 0 < ε) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n))
      {η | ε ≤ |Real.log (decoratedTerminalTotal step H n (x,η) /
        decoratedTerminalTotal step (fun _ => 0) n (x,η))-finiteCascadeLogRecursion ν step n z H x|} ≤
      ENNReal.ofReal (cascadeLogFluctuationConstant n z/ε^2) := by
  simp_rw [decoratedTerminalTotal_zero,decoratedTerminalTotal_telescoping ν step H n z]
  exact decoratedCascade_log_deviation_le ν step hs n z hz hz0 hz1 _
    (finiteCascadeShifts_measurable ν step hs n z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step n z (fun j => (hz0 j).ne') H hI i y).2) x
    (finiteCascadeLogRecursion ν step n z H x) hε

end SphericalPerceptronFreeEnergy

end

end OAI
