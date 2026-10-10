import Mathlib
import OAI.Probability.SKGap.Brownian.ContinuousPosteriorMass

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

def driftSquare (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  ∑i,(mean (posterior q t h) i-mean (posterior p t h) i)^2

lemma driftSquare_nonneg (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0≤driftSquare p q t h := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma driftSquare_le (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    driftSquare p q t h≤4*(n:ℝ) := mean_difference_square_le _ _

lemma continuous_driftSquare (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (driftSquare p q t (k := k)) := by
  unfold driftSquare mean
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_finsetSum _ (fun x _ => (continuous_posterior_mass q t k x).mul_const _)).sub
      (continuous_finsetSum _ (fun x _ => (continuous_posterior_mass p t k x).mul_const _))).pow 2)

lemma integrable_driftSquare_weight (p q : Prior n) (t : ℝ) (k : ℕ) :
    Integrable (fun h : History n k => density q t h*driftSquare p q t h) (reference n k) := by
  apply ((integrable_density q t k).mul_const (4*(n:ℝ))).mono'
    ((continuous_density q t k).mul (continuous_driftSquare p q t k)).aestronglyMeasurable
  filter_upwards [] with h
  change |density q t h*driftSquare p q t h|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos q t h).le (driftSquare_nonneg _ _ _ _))]
  exact mul_le_mul_of_nonneg_left (driftSquare_le p q t h) (density_pos q t h).le

lemma integrable_entropy_increment (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    Integrable (fun h : History n k => density q t h*
      (∫z,GaussianStep.divergenceIntegrand (posterior p t h) (posterior q t h) t z
        ∂GaussianStep.reference n)) (reference n k) := by
  let L : History n k → ℝ := fun h => log (density q t h/density p t h)
  have hL : Measurable L := (continuous_log_ratio p q t k).measurable
  have hiL : Integrable (fun h => density q t h*L h) (reference n k) :=
    integrable_relativeEntropyIntegrand p q hp t k
  have hLift := integrable_lift q ht L hL hiL
  have hi := (integrable_relativeEntropyIntegrand p q hp t (k+1)).sub hLift
  have he : (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-density q t hz*L hz.1) =
      fun hz => density q t hz.1*(GaussianStep.density (posterior q t hz.1) t hz.2*
        log (GaussianStep.density (posterior q t hz.1) t hz.2/GaussianStep.density (posterior p t hz.1) t hz.2)) := by
    funext ⟨h,z⟩
    rw [relativeEntropy_succ]
    dsimp [L]
    ring
  change Integrable (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-
    density q t hz*L hz.1) ((reference n k).prod (GaussianStep.reference n)) at hi
  rw [he] at hi
  have hh := hi.integral_prod_left
  simp_rw [integral_const_mul,GaussianStep.integral_relativeEntropy _ _ ht] at hh
  exact hh

lemma entropy_step_history_bound (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (htn : 4*(n:ℝ)*t≤1) (k : ℕ) :
    entropy p q t (k+1)≤entropy p q t k+
      t*(∫h:History n k,density q t h*driftSquare p q t h ∂reference n k)+64*(n:ℝ)^2*t^2 := by
  rw [entropy_succ p q hp ht]
  have hh := integral_mono (integrable_entropy_increment p q hp ht k)
    (((integrable_driftSquare_weight p q t k).const_mul t).add
      ((integrable_density q t k).mul_const (64*(n:ℝ)^2*t^2)))
      (fun h => (mul_le_mul_of_nonneg_left
        (GaussianStep.entropy_step_bound (posterior p t h) (posterior q t h) ht htn)
        (density_pos q t h).le).trans_eq (by dsimp [driftSquare]; ring))
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_driftSquare_weight p q t k).const_mul t)
      ((integrable_density q t k).mul_const (64*(n:ℝ)^2*t^2)),integral_const_mul,
      integral_mul_const,integral_density q ht,one_mul] at hh
  linarith

lemma drift_integral_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (k : ℕ)
    (B : Set (History n k)) (hB : MeasurableSet B) (W A : ℝ) (hW : 0≤W) (hA : 0≤A)
    (hgood : ∀h:History n k,h∉B → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    (∫h:History n k,density (squarePrior p f hf) t h*driftSquare p (squarePrior p f hf) t h ∂reference n k) ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+
        4*(n:ℝ)*eventProbability (squarePrior p f hf) t B := by
  let q:=squarePrior p f hf
  let N:=avg p (fun x => (f x)^2)
  let d : History n k→ℝ := fun h => density p t h*energy (posterior p t h) f
  have hiD : Integrable d (reference n k) := integrable_posterior_energy_weight p hp t k f
  have hiQ := integrable_density q t k
  have hiB := hiQ.indicator hB
  have hpoint (h : History n k) : density q t h*driftSquare p q t h ≤
      (W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+
        (A*sqrt (n:ℝ)/N)*d h+4*(n:ℝ)*B.indicator (density q t) h := by
    have he := weighted_energy_identity p f hf t h
    change density q t h*(energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)) = d h/N at he
    have hd0 : 0≤d h := mul_nonneg (density_pos p t h).le (energy_nonneg _ _)
    have hconst : 0≤(W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h :=
      mul_nonneg (by positivity) (density_pos q t h).le
    have hdpos : 0≤(A*sqrt (n:ℝ)/N)*d h := mul_nonneg (div_nonneg (mul_nonneg hA (sqrt_nonneg _)) hf.le) hd0
    by_cases hb : h∈B
    · rw [Set.indicator_of_mem hb]
      have hh:=mul_le_mul_of_nonneg_left (driftSquare_le p q t h) (density_pos q t h).le
      nlinarith
    · rw [Set.indicator_of_notMem hb,mul_zero,add_zero]
      have hh:=mul_le_mul_of_nonneg_left (hgood h hb) (density_pos q t h).le
      calc
        _≤density q t h*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) := hh
        _=(W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+A*sqrt (n:ℝ)*
            (density q t h*(energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) := by ring
        _=_ := by rw [he]; ring
  have hi1 := hiQ.const_mul (W*(n:ℝ)+2*A*sqrt (n:ℝ))
  have hi2 := hiD.const_mul (A*sqrt (n:ℝ)/N)
  have hi3 := hiB.const_mul (4*(n:ℝ))
  have hi12 : Integrable (fun h => (W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+
      (A*sqrt (n:ℝ)/N)*d h) (reference n k) := hi1.add hi2
  have hh := integral_mono (integrable_driftSquare_weight p q t k) (hi12.add hi3) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hi12 hi3,integral_add hi1 hi2,integral_const_mul,
    integral_const_mul,integral_const_mul,integral_density q ht,integral_indicator hB,mul_one] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f)
    (show 0≤A*sqrt (n:ℝ)/N from div_nonneg (mul_nonneg hA (sqrt_nonneg _)) hf.le)
  change _≤(W*(n:ℝ)+2*A*sqrt (n:ℝ))+(A*sqrt (n:ℝ)/N)*(∫h,d h ∂reference n k)+
    4*(n:ℝ)*eventProbability q t B at hh
  change (A*sqrt (n:ℝ)/N)*(∫h,d h ∂reference n k)≤(A*sqrt (n:ℝ)/N)*energy p f at hd
  dsimp [N,q] at hh hd
  simp only [div_eq_mul_inv] at hh hd ⊢
  nlinarith

theorem entropy_good_step (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (k : ℕ)
    (B : Set (History n k)) (hB : MeasurableSet B) (W A a : ℝ)
    (hW : 0≤W) (hA : 0≤A) (ha : 0<a)
    (hsmall : eventProbability p t B≤exp (-a*(n:ℝ)))
    (hgood : ∀h:History n k,h∉B → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    entropy p (squarePrior p f hf) t (k+1)≤
      (1+4*t/a)*entropy p (squarePrior p f hf) t k+
        t*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*t^2 := by
  have hs:=entropy_step_history_bound p (squarePrior p f hf) hp ht htn k
  have hd:=mul_le_mul_of_nonneg_left (drift_integral_bound p hp f hf ht k B hB W A hW hA hgood) ht
  have he:=entropy_event_bound p (squarePrior p f hf) hp ht k B hB (a*(n:ℝ))
    (by simpa only [neg_mul] using hsmall)
  have he':=mul_le_mul_of_nonneg_left he (show 0≤4*t/a by positivity)
  have heq : (4*t/a)*(a*(n:ℝ)*eventProbability (squarePrior p f hf) t B)=
      t*(4*(n:ℝ)*eventProbability (squarePrior p f hf) t B) := by field_simp
  rw [heq] at he'
  simp only [div_eq_mul_inv] at hs hd he' ⊢
  nlinarith

end
end SKGap.GaussianHistory

end OAI
