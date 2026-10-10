import Mathlib
import OAI.Probability.SKGap.Localization.Reference

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

lemma var_eq (p : Prior n) (f : Spin n → ℝ) :
    var p f = avg p (fun x => (f x)^2) - (avg p f)^2 := by
  rw [var, avg_shift_square]
  ring

lemma var_le_square (p : Prior n) (f : Spin n → ℝ) :
    var p f ≤ avg p (fun x => (f x)^2) := by rw [var_eq]; linarith [sq_nonneg (avg p f)]

lemma l1_square_le_avg_square (p : Prior n) (f : Spin n → ℝ) :
    (∑ x, |p x*f x|)^2 ≤ avg p (fun x => (f x)^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => sqrt (p x)) (fun x => sqrt (p x)*|f x|)
  have hs : (∑ x, (sqrt (p x))^2) = 1 := by
    simp_rw [sq_sqrt (p.nonneg _)]; exact p.sum_one
  have he : (∑ x, sqrt (p x)*(sqrt (p x)*|f x|)) = ∑ x, |p x*f x| := by
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_assoc, mul_self_sqrt (p.nonneg x), abs_mul, abs_of_nonneg (p.nonneg x)]
  have hf : (∑ x, (sqrt (p x)*|f x|)^2) = avg p (fun x => (f x)^2) := by
    simp only [avg, mul_pow, sq_sqrt (p.nonneg _), sq_abs]
  rw [he, hs, hf, one_mul] at hc
  exact hc

lemma centered_l1_bound (p : Prior n) (f : Spin n → ℝ) :
    (∑ x, |p x*(f x-avg p f)|)^2 ≤ var p f :=
  l1_square_le_avg_square p (fun x => f x-avg p f)

lemma posterior_avg_weight (p : Prior n) (t : ℝ) (z : Fin n → ℝ) (f : Spin n → ℝ) :
    density p t z * avg (posterior p t z) f = ∑ x, (p x*f x)*likelihood t x z := by
  unfold avg posterior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp
  field_simp [(density_pos p t z).ne']

lemma integrable_posterior_avg_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) :
    Integrable (fun z => density p t z * avg (posterior p t z) f) (reference n) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul _)

lemma integral_posterior_avg_weight (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) :
    (∫ z, density p t z * avg (posterior p t z) f ∂reference n) = avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul _)]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  rfl

lemma posterior_variance_identity (p : Prior n) (t : ℝ) (z : Fin n → ℝ) (f : Spin n → ℝ) :
    density p t z * var (posterior p t z) f =
      density p t z * avg (posterior p t z) (fun x => (f x-avg p f)^2) -
        quadraticIntegrand p (fun x => p x*(f x-avg p f)) t z := by
  have ha := posterior_avg_weight p t z (fun x => f x-avg p f)
  have hshift := avg_shift_square (posterior p t z) f (avg p f)
  rw [avg_sub, avg_const] at ha
  rw [var_eq, hshift, quadraticIntegrand, ← ha]
  field_simp [(density_pos p t z).ne']
  ring

lemma integrable_posterior_variance_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) :
    Integrable (fun z => density p t z * var (posterior p t z) f) (reference n) := by
  simp_rw [posterior_variance_identity]
  exact (integrable_posterior_avg_weight p t _).sub (integrable_quadraticIntegrand p _ t)

lemma integral_posterior_variance (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) :
    (∫ z, density p t z * var (posterior p t z) f ∂reference n) =
      var p f - ∫ z, quadraticIntegrand p (fun x => p x*(f x-avg p f)) t z ∂reference n := by
  simp_rw [posterior_variance_identity]
  rw [integral_sub (integrable_posterior_avg_weight p t _)
    (integrable_quadraticIntegrand p _ t), integral_posterior_avg_weight p ht]
  rfl

theorem variance_step_bound (p : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) (f : Spin n → ℝ) :
    var p f - t*(∑ i, (∑ x, p x*(f x-avg p f)*spinValue (x i))^2) -
        16*(n:ℝ)^2*t^2*var p f ≤
      ∫ z, density p t z*var (posterior p t z) f ∂reference n := by
  rw [integral_posterior_variance p ht]
  have hq := quadratic_bound p (fun x => p x*(f x-avg p f)) (avg_center p f) ht htn
  have he := mul_le_mul_of_nonneg_left (centered_l1_bound p f)
    (show 0 ≤ 16*(n:ℝ)^2*t^2 by positivity)
  linarith

lemma scalar_entropy_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ r*log r-r+1 := by
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hr) hr.le
  have hi : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith

lemma scalar_entropy_le_square {r : ℝ} (hr : 0 < r) : r*log r-r+1 ≤ (r-1)^2 := by
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hr) hr.le
  nlinarith

def divergenceIntegrand (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  density q t z * log (density q t z/density p t z) - density q t z + density p t z

lemma divergenceIntegrand_eq (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    divergenceIntegrand p q t z = density p t z *
      ((density q t z/density p t z)*log (density q t z/density p t z)-
        density q t z/density p t z+1) := by
  unfold divergenceIntegrand
  field_simp [(density_pos p t z).ne']

lemma divergenceIntegrand_nonneg (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    0 ≤ divergenceIntegrand p q t z := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos p t z).le
    (scalar_entropy_nonneg (div_pos (density_pos q t z) (density_pos p t z)))

lemma density_sub (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    (∑ x, (q x-p x)*likelihood t x z) = density q t z-density p t z := by
  simp only [sub_mul, Finset.sum_sub_distrib, density]

lemma divergenceIntegrand_le_quadratic (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    divergenceIntegrand p q t z ≤ quadraticIntegrand p (fun x => q x-p x) t z := by
  rw [divergenceIntegrand_eq, quadraticIntegrand, density_sub]
  calc
    _ ≤ density p t z*(density q t z/density p t z-1)^2 :=
      mul_le_mul_of_nonneg_left
        (scalar_entropy_le_square (div_pos (density_pos q t z) (density_pos p t z)))
        (density_pos p t z).le
    _ = _ := by field_simp [(density_pos p t z).ne']

lemma continuous_divergenceIntegrand (p q : Prior n) (t : ℝ) :
    Continuous (divergenceIntegrand p q t) := by
  have hd := (continuous_density q t).div (continuous_density p t)
    (fun z => (density_pos p t z).ne')
  exact (((continuous_density q t).mul (hd.log (fun z =>
    (div_pos (density_pos q t z) (density_pos p t z)).ne'))).sub
      (continuous_density q t)).add (continuous_density p t)

lemma integrable_divergenceIntegrand (p q : Prior n) (t : ℝ) :
    Integrable (divergenceIntegrand p q t) (reference n) := by
  apply (integrable_quadraticIntegrand p (fun x => q x-p x) t).mono'
    (continuous_divergenceIntegrand p q t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (divergenceIntegrand_nonneg p q t z)]
  exact divergenceIntegrand_le_quadratic p q t z

lemma prior_sub_l1 (p q : Prior n) : (∑ x, |q x-p x|) ≤ 2 := by
  calc
    _ ≤ ∑ x, (q x+p x) := Finset.sum_le_sum (fun x _ => by
      simpa only [abs_of_nonneg (q.nonneg x), abs_of_nonneg (p.nonneg x)] using abs_sub (q x) (p x))
    _ = 2 := by rw [Finset.sum_add_distrib, q.sum_one, p.sum_one]; norm_num

lemma prior_sub_sum (p q : Prior n) : (∑ x, (q x-p x)) = 0 := by
  rw [Finset.sum_sub_distrib, q.sum_one, p.sum_one, sub_self]

theorem entropy_step_bound (p q : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) :
    (∫ z, divergenceIntegrand p q t z ∂reference n) ≤
      t*(∑ i, (mean q i-mean p i)^2)+64*(n:ℝ)^2*t^2 := by
  have hmean : (∑ i, (∑ x, (q x-p x)*spinValue (x i))^2) =
      ∑ i, (mean q i-mean p i)^2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mean]
  have he : (∑ x, |q x-p x|)^2 ≤ 4 := by
    have hl : 0 ≤ ∑ x, |q x-p x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    nlinarith [prior_sub_l1 p q]
  calc
    _ ≤ ∫ z, quadraticIntegrand p (fun x => q x-p x) t z ∂reference n :=
      integral_mono (integrable_divergenceIntegrand p q t) (integrable_quadraticIntegrand p _ t)
        (divergenceIntegrand_le_quadratic p q t)
    _ ≤ t*(∑ i, (mean q i-mean p i)^2)+16*(n:ℝ)^2*t^2*(∑ x, |q x-p x|)^2 := by
      simpa only [hmean] using quadratic_bound p (fun x => q x-p x) (prior_sub_sum p q) ht htn
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 16*(n:ℝ)^2*t^2 by positivity)]

lemma integrable_relativeEntropy (p q : Prior n) (t : ℝ) :
    Integrable (fun z => density q t z*log (density q t z/density p t z)) (reference n) := by
  have he : (fun z => density q t z*log (density q t z/density p t z)) =
      fun z => divergenceIntegrand p q t z+density q t z-density p t z := by
    funext z
    unfold divergenceIntegrand
    ring
  rw [he]
  exact ((integrable_divergenceIntegrand p q t).add (integrable_density q t)).sub
    (integrable_density p t)

lemma integral_relativeEntropy (p q : Prior n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density q t z*log (density q t z/density p t z) ∂reference n) =
      ∫ z, divergenceIntegrand p q t z ∂reference n := by
  have hi := integral_add
    ((integrable_relativeEntropy p q t).sub (integrable_density q t)) (integrable_density p t)
  have hj := integral_sub (integrable_relativeEntropy p q t) (integrable_density q t)
  simp only [Pi.sub_apply] at hi hj
  rw [hj, integral_density q ht, integral_density p ht] at hi
  change (∫ z, divergenceIntegrand p q t z ∂reference n) = _ at hi
  linarith

def squarePrior (p : Prior n) (f : Spin n → ℝ) (hf : 0 < avg p (fun x => (f x)^2)) : Prior n where
  mass x := p x*(f x)^2/avg p (fun x => (f x)^2)
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (sq_nonneg _)) hf.le
  sum_one := by rw [← Finset.sum_div]; exact div_self hf.ne'

lemma squarePrior_density (p : Prior n) (f : Spin n → ℝ)
    (hf : 0 < avg p (fun x => (f x)^2)) (t : ℝ) (z : Fin n → ℝ) :
    density (squarePrior p f hf) t z =
      density p t z*avg (posterior p t z) (fun x => (f x)^2)/avg p (fun x => (f x)^2) := by
  rw [posterior_avg_weight]
  unfold density squarePrior
  dsimp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma posterior_square_pos (p : Prior n) (f : Spin n → ℝ)
    (hf : 0 < avg p (fun x => (f x)^2)) (t : ℝ) (z : Fin n → ℝ) :
    0 < avg (posterior p t z) (fun x => (f x)^2) := by
  have h := density_pos (squarePrior p f hf) t z
  rw [squarePrior_density] at h
  exact (mul_pos_iff_of_pos_left (density_pos p t z)).mp ((div_pos_iff_of_pos_right hf).mp h)

lemma squarePrior_posterior (p : Prior n) (f : Spin n → ℝ)
    (hf : 0 < avg p (fun x => (f x)^2)) (t : ℝ) (z : Fin n → ℝ) :
    posterior (squarePrior p f hf) t z =
      squarePrior (posterior p t z) f (posterior_square_pos p f hf t z) := by
  apply Prior.ext
  funext x
  change (p x*(f x)^2/avg p (fun x => (f x)^2))*likelihood t x z /
      density (squarePrior p f hf) t z =
    (p x*likelihood t x z/density p t z)*(f x)^2/avg (posterior p t z) (fun x => (f x)^2)
  rw [squarePrior_density]
  field_simp [hf.ne', (density_pos p t z).ne', (posterior_square_pos p f hf t z).ne']

lemma avg_add (p : Prior n) (f g : Spin n → ℝ) :
    avg p (fun x => f x+g x) = avg p f+avg p g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

lemma avg_const_mul (p : Prior n) (c : ℝ) (f : Spin n → ℝ) :
    avg p (fun x => c*f x) = c*avg p f := by
  simpa only [mul_comm c] using avg_mul_const p f c

lemma avg_nonneg (p : Prior n) (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

def cond (p : Prior n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  (p x*f x+p (flip i x)*f (flip i x))/(p x+p (flip i x))

lemma cond_flip (p : Prior n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    cond p i f (flip i x) = cond p i f x := by
  simp only [cond, flip_flip, add_comm]

lemma avg_flip (p : Prior n) (i : Fin n) (f : Spin n → ℝ) :
    avg p f = (1/2:ℝ)*∑ x, (p x*f x+p (flip i x)*f (flip i x)) := by
  rw [Finset.sum_add_distrib, sum_flip i (fun x => p x*f x)]
  unfold avg
  ring

lemma conditional_orthogonal (p : Prior n) (hp : ∀ x, 0 < p x) (i : Fin n)
    (f c : Spin n → ℝ) (hc : ∀ x, c (flip i x)=c x) :
    avg p (fun x => (f x-cond p i f x)*c x) = 0 := by
  rw [avg_flip p i]
  have hs : (∑ x, (p x*((f x-cond p i f x)*c x)+
      p (flip i x)*((f (flip i x)-cond p i f (flip i x))*c (flip i x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [cond_flip, hc]
    unfold cond
    field_simp [(add_pos (hp x) (hp (flip i x))).ne']
    ring
  rw [hs, mul_zero]

lemma conditional_minimal (p : Prior n) (hp : ∀ x, 0 < p x) (i : Fin n)
    (f c : Spin n → ℝ) (hc : ∀ x, c (flip i x)=c x) :
    avg p (fun x => (f x-cond p i f x)^2) ≤ avg p (fun x => (f x-c x)^2) := by
  have ho := conditional_orthogonal p hp i f (fun x => cond p i f x-c x)
    (fun x => by rw [cond_flip, hc])
  have he (x : Spin n) : (f x-c x)^2 =
      (f x-cond p i f x)^2+(cond p i f x-c x)^2+
        2*((f x-cond p i f x)*(cond p i f x-c x)) := by ring
  simp_rw [he]
  rw [avg_add, avg_add, avg_const_mul, ho, mul_zero, add_zero]
  exact le_add_of_nonneg_right (avg_nonneg p _ (fun _ => sq_nonneg _))

def energy (p : Prior n) (f : Spin n → ℝ) : ℝ :=
  ∑ i, avg p (fun x => (f x-cond p i f x)^2)

lemma energy_nonneg (p : Prior n) (f : Spin n → ℝ) : 0 ≤ energy p f :=
  Finset.sum_nonneg (fun _ _ => avg_nonneg p _ (fun _ => sq_nonneg _))

lemma avg_sum (p : Prior n) {ι : Type*} [Fintype ι] (f : ι → Spin n → ℝ) :
    avg p (fun x => ∑ i, f i x) = ∑ i, avg p (f i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma posterior_mass_pos (p : Prior n) (hp : ∀ x, 0 < p x) (t : ℝ) (z : Fin n → ℝ)
    (x : Spin n) : 0 < posterior p t z x :=
  div_pos (mul_pos (hp x) (likelihood_pos t x z)) (density_pos p t z)

lemma posterior_energy_bound (p : Prior n) (hp : ∀ x, 0 < p x) (t : ℝ) (z : Fin n → ℝ)
    (f : Spin n → ℝ) :
    energy (posterior p t z) f ≤ avg (posterior p t z)
      (fun x => ∑ i, (f x-cond p i f x)^2) := by
  rw [avg_sum]
  exact Finset.sum_le_sum (fun i _ => conditional_minimal (posterior p t z)
    (posterior_mass_pos p hp t z) i f (cond p i f) (cond_flip p i f))

lemma continuous_posterior_mass (p : Prior n) (t : ℝ) (x : Spin n) :
    Continuous (fun z => posterior p t z x) := by
  exact ((continuous_likelihood t x).const_mul (p x)).div (continuous_density p t)
    (fun z => (density_pos p t z).ne')

lemma continuous_posterior_cond (p : Prior n) (hp : ∀ x, 0 < p x) (t : ℝ)
    (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    Continuous (fun z => cond (posterior p t z) i f x) := by
  apply Continuous.div
    (((continuous_posterior_mass p t x).mul_const (f x)).add
      ((continuous_posterior_mass p t (flip i x)).mul_const (f (flip i x))))
    ((continuous_posterior_mass p t x).add (continuous_posterior_mass p t (flip i x)))
  intro z
  exact (add_pos (posterior_mass_pos p hp t z x) (posterior_mass_pos p hp t z (flip i x))).ne'

lemma continuous_posterior_energy (p : Prior n) (hp : ∀ x, 0 < p x) (t : ℝ)
    (f : Spin n → ℝ) : Continuous (fun z => energy (posterior p t z) f) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  exact (continuous_posterior_mass p t x).mul
    ((continuous_const.sub (continuous_posterior_cond p hp t i f x)).pow 2)

lemma integrable_posterior_energy_weight (p : Prior n) (hp : ∀ x, 0 < p x) (t : ℝ)
    (f : Spin n → ℝ) :
    Integrable (fun z => density p t z*energy (posterior p t z) f) (reference n) := by
  apply (integrable_posterior_avg_weight p t (fun x => ∑ i, (f x-cond p i f x)^2)).mono'
    ((continuous_density p t).mul (continuous_posterior_energy p hp t f)).aestronglyMeasurable
  filter_upwards [] with z
  change |density p t z*energy (posterior p t z) f| ≤ _
  rw [abs_of_nonneg (mul_nonneg (density_pos p t z).le (energy_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t z f) (density_pos p t z).le

theorem energy_step_bound (p : Prior n) (hp : ∀ x, 0 < p x) {t : ℝ} (ht : 0 ≤ t)
    (f : Spin n → ℝ) :
    (∫ z, density p t z*energy (posterior p t z) f ∂reference n) ≤ energy p f := by
  let F : Spin n → ℝ := fun x => ∑ i, (f x-cond p i f x)^2
  have hle : (∫ z, density p t z*energy (posterior p t z) f ∂reference n) ≤
      ∫ z, density p t z*avg (posterior p t z) F ∂reference n := by
    apply integral_mono (integrable_posterior_energy_weight p hp t f)
      (integrable_posterior_avg_weight p t F)
    intro z
    exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t z f) (density_pos p t z).le
  rw [integral_posterior_avg_weight p ht] at hle
  change _ ≤ avg p (fun x => ∑ i, (f x-cond p i f x)^2) at hle
  rw [avg_sum] at hle
  exact hle

lemma gibbsPrior_avg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    avg (gibbsPrior g h) f = expectation g h f := rfl

lemma gibbsPrior_var (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    var (gibbsPrior g h) f = variance g h f := rfl

lemma gibbsPrior_cond (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (x : Spin n) :
    cond (gibbsPrior g h) i f x = conditionalExpectation g h i f x := by
  unfold cond gibbsPrior conditionalExpectation
  dsimp
  unfold mass
  field_simp [(partition_pos g h).ne', (add_pos (weight_pos g h x) (weight_pos g h (flip i x))).ne']

lemma gibbsPrior_energy (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    energy (gibbsPrior g h) f = dirichlet g h f := by
  simp only [energy, gibbsPrior_cond, gibbsPrior_avg, dirichlet]

end
end SKGap.GaussianStep

end OAI
