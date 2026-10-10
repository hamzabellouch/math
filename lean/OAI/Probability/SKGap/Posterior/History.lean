import Mathlib
import OAI.Probability.SKGap.Localization.DivergenceIntegrand

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

abbrev History (n : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => History n k × (Fin n → ℝ)

@[reducible] instance historyMeasurable (n : ℕ) : (k : ℕ) → MeasurableSpace (History n k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    change MeasurableSpace (History n k × (Fin n → ℝ))
    letI := historyMeasurable n k
    infer_instance

@[reducible] instance historyTopology (n : ℕ) : (k : ℕ) → TopologicalSpace (History n k)
  | 0 => inferInstanceAs (TopologicalSpace Unit)
  | k+1 => by
    change TopologicalSpace (History n k × (Fin n → ℝ))
    letI := historyTopology n k
    infer_instance

instance historySecondCountable (n : ℕ) : (k : ℕ) → SecondCountableTopology (History n k)
  | 0 => inferInstanceAs (SecondCountableTopology Unit)
  | k+1 => by
    change SecondCountableTopology (History n k × (Fin n → ℝ))
    let := historySecondCountable n k
    infer_instance

instance historyBorel (n : ℕ) : (k : ℕ) → BorelSpace (History n k)
  | 0 => inferInstanceAs (BorelSpace Unit)
  | k+1 => by
    change BorelSpace (History n k × (Fin n → ℝ))
    let := historyBorel n k
    infer_instance

def reference (n : ℕ) : (k : ℕ) → Measure (History n k)
  | 0 => Measure.dirac ()
  | k+1 => (reference n k).prod (GaussianStep.reference n)

instance reference_probability (n : ℕ) : (k : ℕ) → IsProbabilityMeasure (reference n k)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | k+1 => by
    change IsProbabilityMeasure ((reference n k).prod (GaussianStep.reference n))
    let := reference_probability n k
    infer_instance

def likelihood (t : ℝ) (x : Spin n) : {k : ℕ} → History n k → ℝ
  | 0, _ => 1
  | _+1, h => likelihood t x h.1 * GaussianStep.likelihood t x h.2

lemma likelihood_pos (t : ℝ) (x : Spin n) : ∀ {k : ℕ} (h : History n k),
    0 < likelihood t x h
  | 0, _ => zero_lt_one
  | _+1, h => mul_pos (likelihood_pos t x h.1) (GaussianStep.likelihood_pos t x h.2)

lemma continuous_likelihood (t : ℝ) (x : Spin n) : ∀ k,
    Continuous (likelihood t x (k := k))
  | 0 => continuous_const
  | k+1 => (continuous_likelihood t x k).comp continuous_fst |>.mul
      ((GaussianStep.continuous_likelihood t x).comp continuous_snd)

lemma integrable_likelihood (t : ℝ) (x : Spin n) : ∀ k,
    Integrable (likelihood t x (k := k)) (reference n k)
  | 0 => by
    change Integrable (fun _ : Unit => (1:ℝ)) (Measure.dirac ())
    exact integrable_const 1
  | k+1 => (integrable_likelihood t x k).mul_prod (GaussianStep.integrable_likelihood t x)

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : Spin n) : ∀ k,
    (∫ h : History n k, likelihood t x h ∂reference n k) = 1
  | 0 => by
    change (∫ _ : Unit, (1:ℝ) ∂Measure.dirac ()) = 1
    rw [integral_dirac]
  | k+1 => by
    change (∫ h, likelihood t x h.1 * GaussianStep.likelihood t x h.2
      ∂(reference n k).prod (GaussianStep.reference n)) = 1
    rw [integral_prod_mul, integral_likelihood ht x k, GaussianStep.integral_likelihood ht, mul_one]

def density (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  ∑ x, p x*likelihood t x h

lemma density_pos (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0 < density p t h := by
  have he : ∃ x, 0 < p x := by
    by_contra hn
    push Not at hn
    have hz : ∑ x, p x = 0 := Finset.sum_eq_zero (fun x _ => le_antisymm (hn x) (p.nonneg x))
    linarith [p.sum_one]
  obtain ⟨x,hx⟩ := he
  exact Finset.sum_pos' (fun y _ => mul_nonneg (p.nonneg y) (likelihood_pos t y h).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (likelihood_pos t x h)⟩

lemma continuous_density (p : Prior n) (t : ℝ) (k : ℕ) : Continuous (density p t (k := k)) :=
  continuous_finsetSum _ (fun x _ => (continuous_likelihood t x k).const_mul (p x))

lemma integrable_density (p : Prior n) (t : ℝ) (k : ℕ) :
    Integrable (density p t (k := k)) (reference n k) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood t x k).const_mul (p x))

lemma integral_density (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (∫ h : History n k, density p t h ∂reference n k) = 1 := by
  unfold density
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x k).const_mul (p x))]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  exact p.sum_one

def posterior (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : Prior n where
  mass x := p x*likelihood t x h/density p t h
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos t x h).le) (density_pos p t h).le
  sum_one := by rw [← Finset.sum_div]; exact div_self (density_pos p t h).ne'

lemma density_zero (p : Prior n) (t : ℝ) (h : History n 0) : density p t h=1 := by
  simp only [density, likelihood, mul_one, p.sum_one]

lemma posterior_zero (p : Prior n) (t : ℝ) (h : History n 0) : posterior p t h=p := by
  apply Prior.ext
  funext x
  change p x*1/density p t h=p x
  rw [density_zero, mul_one, div_one]

lemma density_succ (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    density p t (k := k+1) (h,z) = density p t h*GaussianStep.density (posterior p t h) t z := by
  change (∑ x, p x*(likelihood t x h*GaussianStep.likelihood t x z)) =
    density p t h*(∑ x, (p x*likelihood t x h/density p t h)*GaussianStep.likelihood t x z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos p t h).ne']

lemma posterior_succ (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    posterior p t (k := k+1) (h,z) = GaussianStep.posterior (posterior p t h) t z := by
  apply Prior.ext
  funext x
  change p x*(likelihood t x h*GaussianStep.likelihood t x z)/density p t (k := k+1) (h,z) =
    (p x*likelihood t x h/density p t h)*GaussianStep.likelihood t x z /
      GaussianStep.density (posterior p t h) t z
  rw [density_succ]
  field_simp [(density_pos p t h).ne', (GaussianStep.density_pos (posterior p t h) t z).ne']

lemma posterior_avg_weight (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (f : Spin n → ℝ) :
    density p t h*avg (posterior p t h) f=∑ x, p x*likelihood t x h*f x := by
  simp only [avg, posterior, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos p t h).ne']

lemma integrable_posterior_avg_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) (k : ℕ) :
    Integrable (fun h : History n k => density p t h*avg (posterior p t h) f) (reference n k) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => ((integrable_likelihood t x k).const_mul (p x)).mul_const (f x))

lemma integral_posterior_avg_weight (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) (k : ℕ) :
    (∫ h : History n k, density p t h*avg (posterior p t h) f ∂reference n k)=avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => ((integrable_likelihood t x k).const_mul (p x)).mul_const (f x))]
  simp_rw [integral_mul_const, integral_const_mul, integral_likelihood ht, mul_one]
  rfl

lemma density_le (p q : Prior n) {B : ℝ} (hB : ∀x, q x ≤ B*p x)
    (t : ℝ) {k : ℕ} (h : History n k) : density q t h ≤ B*density p t h := by
  unfold density
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _ => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hB x) (likelihood_pos t x h).le)

lemma exists_domination (p q : Prior n) (hp : ∀x,0<p x) :
    ∃B:ℝ,0≤B ∧ ∀x,q x≤B*p x := by
  let B := ∑x,q x/p x
  have hnonneg (x : Spin n) : 0≤q x/p x := div_nonneg (q.nonneg x) (hp x).le
  refine ⟨B,Finset.sum_nonneg (fun x _ => hnonneg x),?_⟩
  intro x
  have hle : q x/p x ≤ B := Finset.single_le_sum (fun y _ => hnonneg y) (Finset.mem_univ x)
  exact (div_le_iff₀ (hp x)).mp hle

def relativeEntropyIntegrand (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  density q t h*log (density q t h/density p t h)

def divergenceIntegrand (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  relativeEntropyIntegrand p q t h-density q t h+density p t h

lemma divergenceIntegrand_eq (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    divergenceIntegrand p q t h = density p t h*
      ((density q t h/density p t h)*log (density q t h/density p t h)-
        density q t h/density p t h+1) := by
  unfold divergenceIntegrand relativeEntropyIntegrand
  field_simp [(density_pos p t h).ne']

lemma divergenceIntegrand_nonneg (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0≤divergenceIntegrand p q t h := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos p t h).le
    (scalar_entropy_nonneg (div_pos (density_pos q t h) (density_pos p t h)))

lemma continuous_log_ratio (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (fun h : History n k => log (density q t h/density p t h)) :=
  ((continuous_density q t k).div (continuous_density p t k)
    (fun h => (density_pos p t h).ne')).log
      (fun h => (div_pos (density_pos q t h) (density_pos p t h)).ne')

lemma continuous_relativeEntropyIntegrand (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (relativeEntropyIntegrand p q t (k := k)) :=
  (continuous_density q t k).mul (continuous_log_ratio p q t k)

lemma continuous_divergenceIntegrand (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (divergenceIntegrand p q t (k := k)) :=
  ((continuous_relativeEntropyIntegrand p q t k).sub (continuous_density q t k)).add
    (continuous_density p t k)

lemma integrable_divergenceIntegrand (p q : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ) :
    Integrable (divergenceIntegrand p q t (k := k)) (reference n k) := by
  obtain ⟨B,hB,hdom⟩:=exists_domination p q hp
  apply ((integrable_density p t k).mul_const ((B+1)^2)).mono'
    (continuous_divergenceIntegrand p q t k).aestronglyMeasurable
  filter_upwards [] with h
  change |divergenceIntegrand p q t h|≤density p t h*(B+1)^2
  rw [abs_of_nonneg (divergenceIntegrand_nonneg p q t h), divergenceIntegrand_eq]
  apply mul_le_mul_of_nonneg_left _ (density_pos p t h).le
  have hr : 0<density q t h/density p t h := div_pos (density_pos q t h) (density_pos p t h)
  have hle : density q t h/density p t h≤B :=
    (div_le_iff₀ (density_pos p t h)).mpr (density_le p q hdom t h)
  exact (scalar_entropy_le_square hr).trans (by nlinarith)

lemma integrable_relativeEntropyIntegrand (p q : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ) :
    Integrable (relativeEntropyIntegrand p q t (k := k)) (reference n k) := by
  have hi := ((integrable_divergenceIntegrand p q hp t k).add (integrable_density q t k)).sub
    (integrable_density p t k)
  convert hi using 1
  funext h
  simp only [Pi.sub_apply,Pi.add_apply,divergenceIntegrand]
  ring

def entropy (p q : Prior n) (t : ℝ) (k : ℕ) : ℝ :=
  ∫h:History n k,relativeEntropyIntegrand p q t h ∂reference n k

lemma entropy_eq_divergence (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    entropy p q t k = ∫h:History n k,divergenceIntegrand p q t h ∂reference n k := by
  have hi := integral_add
    ((integrable_relativeEntropyIntegrand p q hp t k).sub (integrable_density q t k))
    (integrable_density p t k)
  have hj := integral_sub (integrable_relativeEntropyIntegrand p q hp t k)
    (integrable_density q t k)
  simp only [Pi.sub_apply] at hi hj
  rw [hj,integral_density p ht,integral_density q ht] at hi
  change (∫h:History n k,divergenceIntegrand p q t h ∂reference n k) = _ at hi
  change (∫h:History n k,relativeEntropyIntegrand p q t h ∂reference n k) = _
  linarith

lemma entropy_nonneg (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    0≤entropy p q t k := by
  rw [entropy_eq_divergence p q hp ht]
  exact integral_nonneg (divergenceIntegrand_nonneg p q t)

lemma entropy_zero (p q : Prior n) (t : ℝ) : entropy p q t 0=0 := by
  unfold entropy relativeEntropyIntegrand
  simp only [density_zero,div_self one_ne_zero,log_one,mul_zero,integral_zero]

lemma integrable_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ} (F : History n k → ℝ)
    (hF : Measurable F) (hi : Integrable (fun h => density p t h*F h) (reference n k)) :
    Integrable (fun h : History n (k+1) => density p t h*F h.1) (reference n (k+1)) := by
  change Integrable (fun h : History n k × (Fin n → ℝ) => density p t (k := k+1) h*F h.1)
    ((reference n k).prod (GaussianStep.reference n))
  apply (integrable_prod_iff (((continuous_density p t (k+1)).measurable.mul
    (hF.comp measurable_fst)).aestronglyMeasurable)).mpr
  constructor
  · filter_upwards [] with h
    change Integrable (fun z => density p t (k := k+1) (h,z)*F h) (GaussianStep.reference n)
    simp_rw [density_succ]
    have he : (fun z => density p t h*GaussianStep.density (posterior p t h) t z*F h) =
        fun z => (density p t h*F h)*GaussianStep.density (posterior p t h) t z := by
      funext z; ring
    rw [he]
    exact (GaussianStep.integrable_density (posterior p t h) t).const_mul _
  · have he (h : History n k) :
        (∫z, ‖density p t (k := k+1) (h,z)*F h‖ ∂GaussianStep.reference n) = ‖density p t h*F h‖ := by
      simp_rw [density_succ,Real.norm_eq_abs,abs_mul,abs_of_pos (density_pos p t h),
        abs_of_pos (GaussianStep.density_pos (posterior p t h) t _)]
      rw [integral_mul_const,integral_const_mul,GaussianStep.integral_density _ ht]
      ring
    change Integrable (fun h : History n k =>
      ∫z, ‖density p t (k := k+1) (h,z)*F h‖ ∂GaussianStep.reference n) (reference n k)
    simp_rw [he]
    exact hi.norm

lemma integral_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ} (F : History n k → ℝ)
    (hF : Measurable F) (hi : Integrable (fun h => density p t h*F h) (reference n k)) :
    (∫h:History n (k+1),density p t h*F h.1 ∂reference n (k+1)) =
      ∫h:History n k,density p t h*F h ∂reference n k := by
  rw [show reference n (k+1)=(reference n k).prod (GaussianStep.reference n) from rfl,
    integral_prod _ (integrable_lift p ht F hF hi)]
  apply integral_congr_ae
  filter_upwards [] with h
  simp_rw [density_succ]
  rw [integral_mul_const,integral_const_mul,GaussianStep.integral_density _ ht,mul_one]

lemma relativeEntropy_succ (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    relativeEntropyIntegrand p q t (k := k+1) (h,z) =
      density q t (k := k+1) (h,z)*log (density q t h/density p t h)+
      density q t h*(GaussianStep.density (posterior q t h) t z *
        log (GaussianStep.density (posterior q t h) t z/GaussianStep.density (posterior p t h) t z)) := by
  unfold relativeEntropyIntegrand
  rw [density_succ,density_succ]
  rw [mul_div_mul_comm,log_mul
    (div_pos (density_pos q t h) (density_pos p t h)).ne'
    (div_pos (GaussianStep.density_pos (posterior q t h) t z)
      (GaussianStep.density_pos (posterior p t h) t z)).ne']
  ring

theorem entropy_succ (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    entropy p q t (k+1) = entropy p q t k+
      ∫h:History n k,density q t h*
        (∫z,GaussianStep.divergenceIntegrand (posterior p t h) (posterior q t h) t z
          ∂GaussianStep.reference n) ∂reference n k := by
  let L : History n k → ℝ := fun h => log (density q t h/density p t h)
  have hL : Measurable L := (continuous_log_ratio p q t k).measurable
  have hiL : Integrable (fun h => density q t h*L h) (reference n k) :=
    integrable_relativeEntropyIntegrand p q hp t k
  have hLift := integrable_lift q ht L hL hiL
  have hi := (integrable_relativeEntropyIntegrand p q hp t (k+1)).sub hLift
  have he : (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz - density q t hz*L hz.1) =
      fun hz => density q t hz.1*(GaussianStep.density (posterior q t hz.1) t hz.2*
        log (GaussianStep.density (posterior q t hz.1) t hz.2/GaussianStep.density (posterior p t hz.1) t hz.2)) := by
    funext ⟨h,z⟩
    rw [relativeEntropy_succ]
    dsimp [L]
    ring
  have hs := integral_sub (integrable_relativeEntropyIntegrand p q hp t (k+1)) hLift
  change (∫hz:History n (k+1),relativeEntropyIntegrand p q t hz-density q t hz*L hz.1
    ∂reference n (k+1)) = _ at hs
  rw [integral_lift q ht L hL hiL] at hs
  change (∫hz:History n (k+1),relativeEntropyIntegrand p q t hz-density q t hz*L hz.1
    ∂reference n (k+1)) = entropy p q t (k+1)-entropy p q t k at hs
  change Integrable (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-
    density q t hz*L hz.1) (reference n (k+1)) at hi
  rw [he] at hi hs
  rw [show reference n (k+1)=(reference n k).prod (GaussianStep.reference n) from rfl,
    integral_prod _ hi] at hs
  simp_rw [integral_const_mul,GaussianStep.integral_relativeEntropy _ _ ht] at hs
  linarith

def law (p : Prior n) (t : ℝ) (k : ℕ) : Measure (History n k) :=
  (reference n k).withDensity (fun h => ENNReal.ofReal (density p t h))

lemma law_probability (p : Prior n) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    IsProbabilityMeasure (law p t k) := by
  constructor
  rw [law,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (integrable_density p t k)
      (ae_of_all _ (fun h => (density_pos p t h).le)),integral_density p ht,ENNReal.ofReal_one]

lemma integral_law (p : Prior n) (t : ℝ) {k : ℕ} (F : History n k → ℝ) :
    (∫h,F h ∂law p t k) = ∫h,density p t h*F h ∂reference n k := by
  rw [law,integral_withDensity_eq_integral_toReal_smul
    ((continuous_density p t k).measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (density_pos p t _).le,smul_eq_mul]

lemma integrable_law_iff (p : Prior n) (t : ℝ) {k : ℕ} (F : History n k → ℝ) :
    Integrable F (law p t k) ↔ Integrable (fun h => density p t h*F h) (reference n k) := by
  rw [law,integrable_withDensity_iff_integrable_smul'
    ((continuous_density p t k).measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (density_pos p t _).le,smul_eq_mul]

def eventProbability (p : Prior n) (t : ℝ) {k : ℕ} (E : Set (History n k)) : ℝ :=
  ∫h in E,density p t h ∂reference n k

lemma eventProbability_nonneg (p : Prior n) (t : ℝ) {k : ℕ} (E : Set (History n k)) :
    0≤eventProbability p t E := integral_nonneg (fun h => (density_pos p t h).le)

lemma eventProbability_eq (p : Prior n) (t : ℝ) {k : ℕ} (E : Set (History n k))
    (hE : MeasurableSet E) : ENNReal.ofReal (eventProbability p t E)=law p t k E := by
  rw [eventProbability,law,withDensity_apply _ hE]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_density p t k).integrableOn
    (ae_of_all _ (fun h => (density_pos p t h).le))

lemma scalar_entropy_fenchel {r : ℝ} (hr : 0<r) (c : ℝ) :
    c*r-exp c+1≤r*log r-r+1 := by
  have he := mul_le_mul_of_nonneg_left (add_one_le_exp (c-log r)) hr.le
  have hx : r*exp (c-log r)=exp c := by
    rw [exp_sub,exp_log hr]
    field_simp
  rw [hx] at he
  nlinarith

theorem entropy_event_bound (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (k : ℕ) (E : Set (History n k)) (hE : MeasurableSet E) (c : ℝ)
    (hsmall : eventProbability p t E≤exp (-c)) :
    c*eventProbability q t E ≤ entropy p q t k+1 := by
  have hpoint (h : History n k) :
      c*E.indicator (density q t) h ≤ divergenceIntegrand p q t h+
        exp c*E.indicator (density p t) h := by
    by_cases he : h∈E
    · rw [Set.indicator_of_mem he,Set.indicator_of_mem he,divergenceIntegrand_eq]
      have hf := mul_le_mul_of_nonneg_left
        (scalar_entropy_fenchel (div_pos (density_pos q t h) (density_pos p t h)) c)
        (density_pos p t h).le
      have hd : density p t h*(density q t h/density p t h)=density q t h :=
        mul_div_cancel₀ _ (density_pos p t h).ne'
      have hmul : density p t h*(c*(density q t h/density p t h))=c*density q t h := by
        rw [←mul_assoc, mul_comm (density p t h) c,mul_assoc,hd]
      nlinarith [density_pos p t h]
    · rw [Set.indicator_of_notMem he,Set.indicator_of_notMem he,mul_zero,mul_zero,add_zero]
      exact divergenceIntegrand_nonneg p q t h
  have hi := integral_mono (((integrable_density q t k).indicator hE).const_mul c)
    ((integrable_divergenceIntegrand p q hp t k).add
      (((integrable_density p t k).indicator hE).const_mul (exp c))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (integrable_divergenceIntegrand p q hp t k)
      (((integrable_density p t k).indicator hE).const_mul (exp c)),integral_const_mul,
    integral_indicator hE,integral_indicator hE,←entropy_eq_divergence p q hp ht] at hi
  change c*eventProbability q t E≤entropy p q t k+exp c*eventProbability p t E at hi
  have hm := mul_le_mul_of_nonneg_left hsmall (exp_pos c).le
  rw [←exp_add,add_neg_cancel,exp_zero] at hm
  linarith

end
end SKGap.GaussianHistory

end OAI
