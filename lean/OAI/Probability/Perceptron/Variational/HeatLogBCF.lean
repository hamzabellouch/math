import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianAverage

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma heatLog_continuous (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : Continuous (heatLog s d f) := by
  change Continuous (fun x => heatLog s d f x)
  by_cases hd : d = 0
  · simpa [heatLog, hd] using gaussianAverage_continuous s f
  · have hh := (gaussianAverage_continuous s (expBCF d f)).log (fun x => (gaussianAverage_exp_pos s d f x).ne')
    simpa only [heatLog, hd, ↓reduceIte] using hh.const_mul (d : ℝ)⁻¹

def heatLogBCF (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨heatLog s d f, heatLog_continuous s d f⟩
    (2*‖f‖) (by
      intro x y; change |heatLog s d f x - heatLog s d f y| ≤ 2 * ‖f‖
      exact (abs_sub _ _).trans (by linarith [heatLog_abs_le s d f x, heatLog_abs_le s d f y]))

@[simp] lemma heatLogBCF_coe (s d : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (heatLogBCF s d f : ℝ → ℝ) = heatLog s d f := rfl

lemma exp_heatLog (s d : ℝ≥0) (hd : d ≠ 0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    Real.exp (d * heatLog s d f x) = gaussianAverage s (expBCF d f) x := by
  simp only [heatLog, hd, ↓reduceIte]
  rw [← mul_assoc, mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr hd), one_mul,
    Real.exp_log (gaussianAverage_exp_pos s d f x)]

lemma heatLog_zero (d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) : heatLog 0 d f x = f x := by
  by_cases hd : d = 0
  · simp [heatLog, hd]
  · simp [heatLog, hd]

lemma heatLog_semigroup (s t d : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    heatLog s d (heatLogBCF t d f) x = heatLog (s+t) d f x := by
  by_cases hd : d = 0
  · subst d
    have he : heatLogBCF t 0 f = gaussianAverageBCF t f := by ext z; simp [heatLog]
    simp only [heatLog, ↓reduceIte, he]
    exact gaussianAverage_semigroup s t f x
  · have he : expBCF d (heatLogBCF t d f) = gaussianAverageBCF t (expBCF d f) := by
      ext z
      exact exp_heatLog t d hd f z
    simp only [heatLog, hd, ↓reduceIte, he, gaussianAverage_semigroup]

structure Jet3 where
  f : ℝ →ᵇ ℝ
  d1 : ℝ →ᵇ ℝ
  d2 : ℝ →ᵇ ℝ
  d3 : ℝ →ᵇ ℝ
  has1 : ∀ x, HasDerivAt (f : ℝ → ℝ) (d1 x) x
  has2 : ∀ x, HasDerivAt (d1 : ℝ → ℝ) (d2 x) x
  has3 : ∀ x, HasDerivAt (d2 : ℝ → ℝ) (d3 x) x

lemma Jet3.deriv_eq (g : Jet3) : deriv (g.f : ℝ → ℝ) = g.d1 := funext fun x => (g.has1 x).deriv
lemma Jet3.deriv2_eq (g : Jet3) : iteratedDeriv 2 (g.f : ℝ → ℝ) = g.d2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, g.deriv_eq]
  exact funext fun x => (g.has2 x).deriv
lemma Jet3.deriv3_eq (g : Jet3) : iteratedDeriv 3 (g.f : ℝ → ℝ) = g.d3 := by
  rw [iteratedDeriv_succ, g.deriv2_eq]
  exact funext fun x => (g.has3 x).deriv

lemma Jet3.contDiff (g : Jet3) : ContDiff ℝ 3 (g.f : ℝ → ℝ) := by
  rw [show (3 : WithTop ℕ∞) = 2+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has1 x).differentiableAt, by norm_num, ?_⟩
  rw [g.deriv_eq, show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has2 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d1 : ℝ → ℝ) = g.d2 from funext fun x => (g.has2 x).deriv,
    show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x => (g.has3 x).differentiableAt, by norm_num, ?_⟩
  rw [show deriv (g.d2 : ℝ → ℝ) = g.d3 from funext fun x => (g.has3 x).deriv]
  exact contDiff_zero.mpr g.d3.continuous

def Jet3.gaussianAverage (s : ℝ≥0) (g : Jet3) : Jet3 where
  f := gaussianAverageBCF s g.f
  d1 := gaussianAverageBCF s g.d1
  d2 := gaussianAverageBCF s g.d2
  d3 := gaussianAverageBCF s g.d3
  has1 := gaussianAverage_hasDerivAt s g.f g.d1 g.has1
  has2 := gaussianAverage_hasDerivAt s g.d1 g.d2 g.has2
  has3 := gaussianAverage_hasDerivAt s g.d2 g.d3 g.has3

lemma Jet3.gaussianAverage_norms (s : ℝ≥0) (g : Jet3) :
    ‖(g.gaussianAverage s).f‖ ≤ ‖g.f‖ ∧ ‖(g.gaussianAverage s).d1‖ ≤ ‖g.d1‖ ∧
    ‖(g.gaussianAverage s).d2‖ ≤ ‖g.d2‖ ∧ ‖(g.gaussianAverage s).d3‖ ≤ ‖g.d3‖ := by
  have hh (f : ℝ →ᵇ ℝ) : ‖gaussianAverageBCF s f‖ ≤ ‖f‖ := by
    rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
    intro x; exact gaussianAverage_abs_le s f x
  exact ⟨hh _,hh _,hh _,hh _⟩

def Jet3.exp (d : ℝ) (g : Jet3) : Jet3 where
  f := expBCF d g.f
  d1 := d • (expBCF d g.f * g.d1)
  d2 := expBCF d g.f * (d^2 • (g.d1^2) + d • g.d2)
  d3 := expBCF d g.f * (d^3 • (g.d1^3) + (3*d^2) • (g.d1*g.d2) + d • g.d3)
  has1 x := by
    convert! ((g.has1 x).const_mul d).exp using 1
    dsimp [expBCF]
    ring
  has2 x := by
    have he := ((g.has1 x).const_mul d).exp
    have h := (he.mul (g.has2 x)).const_mul d
    convert! h using 1
    dsimp [expBCF]; ring
  has3 x := by
    have he := ((g.has1 x).const_mul d).exp
    have h := he.mul (((g.has2 x).pow 2).const_mul (d^2) |>.add ((g.has3 x).const_mul d))
    convert! h using 1
    dsimp [expBCF]; ring

lemma inv_bcf_bound {g : ℝ →ᵇ ℝ} {c : ℝ} (hc : 0 < c) (hg : ∀ x, c ≤ g x) (x : ℝ) :
    |(g x)⁻¹| ≤ c⁻¹ := by
  rw [abs_of_pos (inv_pos.mpr (hc.trans_le (hg x)))]
  exact inv_anti₀ hc (hg x)

def invBCF (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (g x)⁻¹, g.continuous.inv₀ (fun x => (hc.trans_le (hg x)).ne')⟩
    (2*c⁻¹) (by
      intro x y; change |(g x)⁻¹ - (g y)⁻¹| ≤ 2*c⁻¹
      exact (abs_sub _ _).trans (by linarith [inv_bcf_bound hc hg x, inv_bcf_bound hc hg y]))

@[simp] lemma invBCF_apply (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) (x : ℝ) :
    invBCF g c hc hg x = (g x)⁻¹ := rfl

lemma invBCF_norm_le (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) :
    ‖invBCF g c hc hg‖ ≤ c⁻¹ := by
  rw [BoundedContinuousFunction.norm_le (inv_nonneg.mpr hc.le)]
  intro x; exact inv_bcf_bound hc hg x

lemma invBCF_hasDerivAt (g g' : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x)
    (hder : ∀ x, HasDerivAt (g : ℝ → ℝ) (g' x) x) (x : ℝ) :
    HasDerivAt (invBCF g c hc hg : ℝ → ℝ) (- g' x * (invBCF g c hc hg x)^2) x := by
  convert! (hder x).inv (hc.trans_le (hg x)).ne' using 1
  simp only [invBCF_apply, div_eq_mul_inv, inv_pow]

def Jet3.heatLogPos (s d : ℝ≥0) (hd : d ≠ 0) (g : Jet3) : Jet3 :=
  let A := (g.exp d).gaussianAverage s
  let c := Real.exp (-d * ‖g.f‖)
  let hc : 0 < c := Real.exp_pos _
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  { f := heatLogBCF s d g.f
    d1 := (d : ℝ)⁻¹ • (A.d1 * J)
    d2 := (d : ℝ)⁻¹ • (A.d2 * J - A.d1^2 * J^2)
    d3 := (d : ℝ)⁻¹ • (A.d3 * J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))
    has1 x := by
      have hh := ((A.has1 x).log (hc.trans_le (hA x)).ne').const_mul (d : ℝ)⁻¹
      convert! hh using 1
      · ext y
        simp only [heatLogBCF_coe, heatLog, hd, ↓reduceIte]
        rfl
    has2 x := by
      have hi := invBCF_hasDerivAt A.f A.d1 c hc hA A.has1 x
      have hh := ((A.has2 x).mul hi).const_mul (d : ℝ)⁻¹
      convert! hh using 1
      dsimp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mul,
        BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_pow,
        Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
      ring
    has3 x := by
      have hi := invBCF_hasDerivAt A.f A.d1 c hc hA A.has1 x
      have hh := (((A.has3 x).mul hi).sub (((A.has2 x).pow 2).mul (hi.pow 2))).const_mul (d : ℝ)⁻¹
      convert! hh using 1
      dsimp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mul,
        BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_add,
        BoundedContinuousFunction.coe_pow, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
        Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
      ring }

def Jet3.heatLog (s d : ℝ≥0) (g : Jet3) : Jet3 :=
  if hd : d = 0 then g.gaussianAverage s else g.heatLogPos s d hd

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptronFreeEnergy.heatLog]
  · rfl

lemma gaussianAverage_jet_error (s : ℝ≥0) (g : Jet3) (x : ℝ) :
    |gaussianAverage s g.f x - g.f x - (s : ℝ)/2 * g.d2 x| ≤
      ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by
  have hh := gaussian_taylor_mean_bound (P := gaussianReal 0 s) g.f g.contDiff
    ‖g.d1‖ ‖g.d2‖ ‖g.d3‖
    (fun y => by rw [g.deriv_eq]; exact g.d1.norm_coe_le_norm y)
    (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y)
    (fun y => by rw [g.deriv3_eq]; exact g.d3.norm_coe_le_norm y)
    (X := fun _ : ℝ => x) aemeasurable_const (Z := id) HasLaw.id (indepFun_const_left _ _)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, g.deriv2_eq, gaussianAverage, id_eq] using hh

lemma log_linear_error_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b - Real.log a - (b-a)/a| ≤ (b-a)^2 / c^2 := by
  have ha0 := hc.trans_le ha
  have hb0 := hc.trans_le hb
  have hu := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hu
  rw [Real.log_div ha0.ne' hb0.ne'] at hl
  have heq : b/a-1 = (b-a)/a := by field_simp
  rw [heq] at hu
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  have hlin : -(Real.log b - Real.log a - (b-a)/a) ≤ (b-a)^2/(a*b) := by
    have he : (b-a)/a + (a/b-1) = (b-a)^2/(a*b) := by field_simp; ring
    linarith
  exact hlin.trans (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hc)
    (by nlinarith [mul_le_mul ha hb hc.le ha0.le]))

lemma gaussianAverage_ge_const (s : ℝ≥0) (f : ℝ →ᵇ ℝ) {c : ℝ}
    (hc : ∀ x, c ≤ f x) (x : ℝ) : c ≤ gaussianAverage s f x := by
  have hh := integral_mono (integrable_const c) (gaussianAverage_integrable s f x) (fun z => hc (x+z))
  simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma log_gaussian_generator_error (g : Jet3) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x, c ≤ g.f x) (C₂ C₃ : ℝ≥0) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃)
    (s : ℝ≥0) (hs : s ≤ 1) (x : ℝ) :
    |Real.log (gaussianAverage s g.f x) - Real.log (g.f x) -
      (s : ℝ)/2 * g.d2 x / g.f x| ≤
      (((C₂ : ℝ)/2 + (C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))^2/c^2 +
        ((C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))/c) * (s : ℝ) * Real.sqrt s := by
  let A := gaussianAverage s g.f x
  let a := g.f x
  let K := (C₃ : ℝ)/6 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  let D := (C₂ : ℝ)/2 + K
  have ha := hg x
  have hA := gaussianAverage_ge_const s g.f hg x
  have hM : 0 ≤ ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := integral_nonneg (fun z => by positivity)
  have hK : 0 ≤ K := by positivity
  have hD : 0 ≤ D := by positivity
  have hs0 : 0 ≤ (s : ℝ) := s.coe_nonneg
  have hs1 : (s : ℝ) ≤ 1 := hs
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := (Real.sqrt_le_one).mpr hs1
  have hrsq := Real.sq_sqrt hs0
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ) * Real.sqrt (s : ℝ) := by nlinarith
  have herr : |A-a-(s : ℝ)/2*g.d2 x| ≤ K * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by gcongr
      _ = _ := by rw [hrcube]; unfold K; ring
  have hdx : |g.d2 x| ≤ C₂ := (g.d2.norm_coe_le_norm x).trans h₂
  have hdelta : |A-a| ≤ D * (s : ℝ) := by
    have habs := abs_add_le (A-a-(s : ℝ)/2*g.d2 x) ((s : ℝ)/2*g.d2 x)
    rw [sub_add_cancel] at habs
    have hterm : |(s : ℝ)/2*g.d2 x| ≤ (s : ℝ)/2*C₂ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s/2)]
      exact mul_le_mul_of_nonneg_left hdx (by positivity)
    have hkr := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hK hs0)
    dsimp [D]; nlinarith
  have hquad : (A-a)^2/c^2 ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s := by
    have hdsq : (A-a)^2 ≤ (D*(s : ℝ))^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (A-a)) (mul_nonneg hD hs0)).mpr hdelta
      simpa only [sq_abs] using hh
    calc
      _ ≤ (D*(s : ℝ))^2/c^2 := div_le_div_of_nonneg_right hdsq (sq_nonneg c)
      _ = D^2/c^2 * (s : ℝ)^2 := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsr hs0)
          (show 0 ≤ D^2/c^2 by positivity)
        nlinarith only [hh]
  have hrem : |A-a-(s : ℝ)/2*g.d2 x|/a ≤ (K/c) * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ (K*(s : ℝ)*Real.sqrt s)/c := div_le_div₀ (by positivity) herr hc ha
      _ = _ := by ring
  have hlog := log_linear_error_le hc ha hA
  change |Real.log A - Real.log a - (s : ℝ)/2*g.d2 x/a| ≤ _
  calc
    _ = |(Real.log A-Real.log a-(A-a)/a) + (A-a-(s : ℝ)/2*g.d2 x)/a| := by congr 1; ring
    _ ≤ |Real.log A-Real.log a-(A-a)/a| + |(A-a-(s : ℝ)/2*g.d2 x)/a| := abs_add_le _ _
    _ = |Real.log A-Real.log a-(A-a)/a| + |A-a-(s : ℝ)/2*g.d2 x|/a := by
      rw [abs_div, abs_of_pos (hc.trans_le ha)]
    _ ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s + (K/c)*(s : ℝ)*Real.sqrt s :=
      add_le_add (hlog.trans hquad) hrem
    _ = _ := by dsimp [D,K]; ring

lemma expBCF_norm_le (d : ℝ) (f : ℝ →ᵇ ℝ) :
    ‖expBCF d f‖ ≤ Real.exp (|d| * ‖f‖) := by
  rw [BoundedContinuousFunction.norm_le (Real.exp_pos _).le]
  exact exp_bcf_bound d f

lemma Jet3.exp_norms (g : Jet3) (d C₀ C₁ C₂ C₃ : ℝ≥0)
    (h₀ : ‖g.f‖ ≤ C₀) (h₁ : ‖g.d1‖ ≤ C₁) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃) :
    let E := Real.exp ((d : ℝ)*C₀)
    ‖(g.exp d).f‖ ≤ E ∧ ‖(g.exp d).d1‖ ≤ (d : ℝ)*E*C₁ ∧
    ‖(g.exp d).d2‖ ≤ E*((d : ℝ)^2*C₁^2 + d*C₂) ∧
    ‖(g.exp d).d3‖ ≤ E*((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*C₁*C₂ + d*C₃) := by
  dsimp only
  have hf : ‖expBCF d g.f‖ ≤ Real.exp ((d : ℝ)*C₀) := by
    refine (expBCF_norm_le d g.f).trans ?_
    rw [abs_of_nonneg d.coe_nonneg]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h₀ d.coe_nonneg)
  refine ⟨hf, ?_, ?_, ?_⟩
  · change ‖(d : ℝ) • (expBCF d g.f * g.d1)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ) * (‖expBCF d g.f‖ * ‖g.d1‖) := by gcongr; exact norm_mul_le _ _
      _ ≤ (d : ℝ) * (Real.exp ((d : ℝ)*C₀) * C₁) := by gcongr
      _ = _ := by ring
  · change ‖expBCF d g.f * ((d : ℝ)^2 • (g.d1^2) + (d : ℝ) • g.d2)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * (‖(d : ℝ)^2 • (g.d1^2)‖ + ‖(d : ℝ) • g.d2‖) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^2 * ‖g.d1^2‖ + (d : ℝ) * ‖g.d2‖) := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg d.coe_nonneg, abs_pow]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^2 * C₁^2 + (d : ℝ) * C₂) := by
        gcongr
        exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖expBCF d g.f * ((d : ℝ)^3 • (g.d1^3) + (3*(d : ℝ)^2) • (g.d1*g.d2) + (d : ℝ) • g.d3)‖ ≤ _
    calc
      _ ≤ ‖expBCF d g.f‖ * ((‖(d : ℝ)^3 • (g.d1^3)‖ + ‖(3*(d : ℝ)^2) • (g.d1*g.d2)‖) + ‖(d : ℝ) • g.d3‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖expBCF d g.f‖ * ((d : ℝ)^3 * ‖g.d1^3‖ + 3*(d : ℝ)^2*‖g.d1*g.d2‖ + (d : ℝ)*‖g.d3‖) := by
        simp only [norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)^3),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3*(d : ℝ)^2), abs_of_nonneg d.coe_nonneg]
      _ ≤ Real.exp ((d : ℝ)*C₀) * ((d : ℝ)^3*C₁^3 + 3*(d : ℝ)^2*(C₁*C₂) + (d : ℝ)*C₃) := by
        gcongr
        · exact (norm_pow_le _ _).trans (by gcongr)
        · exact (norm_mul_le _ _).trans (by gcongr)
      _ = _ := by ring

lemma Jet3.heatLog_uniform_bounds (d : ℝ≥0) (g : Jet3) :
    ∃ C₀ C₁ C₂ C₃ : ℝ≥0, ∀ s : ℝ≥0,
      ‖(g.heatLog s d).f‖ ≤ C₀ ∧ ‖(g.heatLog s d).d1‖ ≤ C₁ ∧
      ‖(g.heatLog s d).d2‖ ≤ C₂ ∧ ‖(g.heatLog s d).d3‖ ≤ C₃ := by
  by_cases hd : d = 0
  · subst d
    refine ⟨‖g.f‖₊, ‖g.d1‖₊, ‖g.d2‖₊, ‖g.d3‖₊, ?_⟩
    intro s; simpa only [Jet3.heatLog, ↓reduceDIte, coe_nnnorm] using g.gaussianAverage_norms s
  let e := g.exp d
  let B := (Real.exp (-(d : ℝ)*‖g.f‖))⁻¹
  let r := (d : ℝ)⁻¹
  have hB : 0 ≤ B := by positivity
  have hr : 0 ≤ r := by positivity
  refine ⟨‖g.f‖₊,
    ⟨r*(‖e.d1‖*B), by positivity⟩,
    ⟨r*(‖e.d2‖*B+‖e.d1‖^2*B^2), by positivity⟩,
    ⟨r*(‖e.d3‖*B+3*(‖e.d1‖*‖e.d2‖*B^2)+2*(‖e.d1‖^3*B^3)), by positivity⟩, ?_⟩
  intro s
  let A := e.gaussianAverage s
  let c := Real.exp (-(d : ℝ)*‖g.f‖)
  let hc := Real.exp_pos (-(d : ℝ)*‖g.f‖)
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  have hj : ‖J‖ ≤ B := invBCF_norm_le A.f c hc hA
  obtain ⟨_, h₁,h₂,h₃⟩ := e.gaussianAverage_norms s
  have hf : ‖(g.heatLog s d).f‖ ≤ ‖g.f‖ := by
    rw [g.heatLog_f, BoundedContinuousFunction.norm_le (norm_nonneg _)]
    exact heatLog_abs_le s d g.f
  rw [Jet3.heatLog, dite_eq_right hd]
  refine ⟨by simpa only [Jet3.heatLog, dite_eq_right hd, coe_nnnorm] using hf, ?_, ?_, ?_⟩
  · change ‖r • (A.d1*J)‖ ≤ r * (‖e.d1‖*B)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (by gcongr)) hr
  · change ‖r • (A.d2*J - A.d1^2*J^2)‖ ≤ r*(‖e.d2‖*B+‖e.d1‖^2*B^2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    gcongr
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
  · change ‖r • (A.d3*J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact (norm_mul_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_mul_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)
    · rw [norm_smul]; norm_num [Real.norm_eq_abs]
      refine (norm_mul_le _ _).trans ?_
      gcongr
      · exact (norm_pow_le _ _).trans (by gcongr)
      · exact (norm_pow_le _ _).trans (by gcongr)

lemma heatLog_generator_uniform (d C₀ C₁ C₂ C₃ : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (g : Jet3), ‖g.f‖ ≤ C₀ → ‖g.d1‖ ≤ C₁ →
      ‖g.d2‖ ≤ C₂ → ‖g.d3‖ ≤ C₃ → ∀ (s : ℝ≥0), s ≤ 1 → ∀ x : ℝ,
        |heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)| ≤
          (C : ℝ) * (s : ℝ) * Real.sqrt s := by
  let M := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  have hM : 0 ≤ M := integral_nonneg (fun z => by positivity)
  by_cases hd : d = 0
  · subst d
    refine ⟨⟨(C₃ : ℝ)/6*M, by positivity⟩, ?_⟩
    intro g _ _ _ h₃ s _ x
    simp only [heatLog, ↓reduceIte, NNReal.coe_zero, zero_mul, add_zero]
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * M := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * M := by gcongr
      _ = (C₃ : ℝ)/6*M * (s : ℝ) * Real.sqrt s := by
        have hh := Real.sq_sqrt s.coe_nonneg
        calc
          _ = (C₃ : ℝ)/6*M * (Real.sqrt s)^2 * Real.sqrt s := by ring
          _ = _ := by rw [hh]
  let c := Real.exp (-(d : ℝ)*C₀)
  let E := Real.exp ((d : ℝ)*C₀)
  let E₂ : ℝ≥0 := ⟨E*((d : ℝ)^2*C₁^2+(d : ℝ)*C₂), by positivity⟩
  let E₃ : ℝ≥0 := ⟨E*((d : ℝ)^3*C₁^3+3*(d : ℝ)^2*C₁*C₂+(d : ℝ)*C₃), by positivity⟩
  let K := ((E₂ : ℝ)/2+(E₃ : ℝ)/6*M)^2/c^2 + ((E₃ : ℝ)/6*M)/c
  have hc : 0 < c := Real.exp_pos _
  have hK : 0 ≤ K := by positivity
  have hdpos : (0 : ℝ) < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd)
  refine ⟨⟨(d : ℝ)⁻¹*K, by positivity⟩, ?_⟩
  intro g h₀ h₁ h₂ h₃ s hs x
  have hh := g.exp_norms d C₀ C₁ C₂ C₃ h₀ h₁ h₂ h₃
  have hlo (x : ℝ) : c ≤ (g.exp d).f x := by
    change Real.exp (-(d : ℝ)*C₀) ≤ Real.exp ((d : ℝ)*g.f x)
    apply Real.exp_le_exp.mpr
    have hb : |g.f x| ≤ C₀ := (g.f.norm_coe_le_norm x).trans h₀
    nlinarith [(abs_le.mp hb).1]
  have herr := log_gaussian_generator_error (g.exp d) c hc hlo E₂ E₃ hh.2.2.1 hh.2.2.2 s hs x
  have he : (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x =
      (d : ℝ) * ((s : ℝ)/2 * (g.d2 x + (d : ℝ)*(g.d1 x)^2)) := by
    change (s : ℝ)/2 * (Real.exp ((d : ℝ)*g.f x) * ((d : ℝ)^2*g.d1 x^2 + (d : ℝ)*g.d2 x)) /
      Real.exp ((d : ℝ)*g.f x) = _
    field_simp
    ring
  have hid : heatLog s d g.f x - g.f x - (s : ℝ)/2 * (g.d2 x+(d : ℝ)*g.d1 x^2) =
      (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (g.exp d).f x) - Real.log ((g.exp d).f x) -
        (s : ℝ)/2 * (g.exp d).d2 x / (g.exp d).f x) := by
    rw [he]
    change _ = (d : ℝ)⁻¹ * (Real.log (gaussianAverage s (expBCF d g.f) x) -
      Real.log (Real.exp ((d : ℝ)*g.f x)) - _)
    rw [Real.log_exp]
    simp only [heatLog, hd, ↓reduceIte]
    field_simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hdpos)]
  calc
    _ ≤ (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr hdpos.le)
    _ = _ := by change (d : ℝ)⁻¹ * (K*(s : ℝ)*Real.sqrt s) = (d : ℝ)⁻¹*K*(s : ℝ)*Real.sqrt s; ring

end SphericalPerceptronFreeEnergy
end

end OAI
