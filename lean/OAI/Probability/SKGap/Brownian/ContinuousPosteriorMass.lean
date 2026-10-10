import Mathlib
import OAI.Probability.SKGap.Posterior.History

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma continuous_posterior_mass (p : Prior n) (t : ℝ) (k : ℕ) (x : Spin n) :
    Continuous (fun h : History n k => posterior p t h x) :=
  ((continuous_likelihood t x k).const_mul (p x)).div (continuous_density p t k)
    (fun h => (density_pos p t h).ne')

lemma continuous_posterior_avg (p : Prior n) (t : ℝ) (k : ℕ) (f : Spin n→ℝ) :
    Continuous (fun h : History n k => avg (posterior p t h) f) :=
  continuous_finsetSum _ (fun x _ => (continuous_posterior_mass p t k x).mul_const (f x))

lemma continuous_posterior_var (p : Prior n) (t : ℝ) (k : ℕ) (f : Spin n→ℝ) :
    Continuous (fun h : History n k => var (posterior p t h) f) := by
  simp_rw [var_eq]
  exact (continuous_posterior_avg p t k _).sub ((continuous_posterior_avg p t k f).pow 2)

lemma integrable_posterior_var_weight (p : Prior n) (t : ℝ) (k : ℕ) (f : Spin n→ℝ) :
    Integrable (fun h : History n k => density p t h*var (posterior p t h) f) (reference n k) := by
  apply (integrable_posterior_avg_weight p t (fun x => (f x)^2) k).mono'
    ((continuous_density p t k).mul (continuous_posterior_var p t k f)).aestronglyMeasurable
  filter_upwards [] with h
  change |density p t h*var (posterior p t h) f| ≤ _
  rw [abs_of_nonneg (mul_nonneg (density_pos p t h).le (var_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (var_le_square _ _) (density_pos p t h).le

lemma posterior_mass_pos (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) {k : ℕ} (h : History n k)
    (x : Spin n) : 0<posterior p t h x :=
  div_pos (mul_pos (hp x) (likelihood_pos t x h)) (density_pos p t h)

lemma posterior_energy_bound (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) {k : ℕ} (h : History n k)
    (f : Spin n→ℝ) : energy (posterior p t h) f ≤
      avg (posterior p t h) (fun x => ∑i,(f x-cond p i f x)^2) := by
  rw [avg_sum]
  exact Finset.sum_le_sum (fun i _ => conditional_minimal (posterior p t h)
    (posterior_mass_pos p hp t h) i f (cond p i f) (cond_flip p i f))

lemma continuous_posterior_cond (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    Continuous (fun h : History n k => cond (posterior p t h) i f x) := by
  apply Continuous.div
    (((continuous_posterior_mass p t k x).mul_const (f x)).add
      ((continuous_posterior_mass p t k (flip i x)).mul_const (f (flip i x))))
    ((continuous_posterior_mass p t k x).add (continuous_posterior_mass p t k (flip i x)))
  intro h
  exact (add_pos (posterior_mass_pos p hp t h x) (posterior_mass_pos p hp t h (flip i x))).ne'

lemma continuous_posterior_energy (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (f : Spin n→ℝ) : Continuous (fun h : History n k => energy (posterior p t h) f) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  exact (continuous_posterior_mass p t k x).mul
    ((continuous_const.sub (continuous_posterior_cond p hp t k i f x)).pow 2)

lemma integrable_posterior_energy_weight (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (f : Spin n→ℝ) :
    Integrable (fun h : History n k => density p t h*energy (posterior p t h) f) (reference n k) := by
  apply (integrable_posterior_avg_weight p t (fun x => ∑i,(f x-cond p i f x)^2) k).mono'
    ((continuous_density p t k).mul (continuous_posterior_energy p hp t k f)).aestronglyMeasurable
  filter_upwards [] with h
  change |density p t h*energy (posterior p t h) f|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos p t h).le (energy_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t h f) (density_pos p t h).le

theorem energy_history_bound (p : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (k : ℕ) (f : Spin n→ℝ) :
    (∫h:History n k,density p t h*energy (posterior p t h) f ∂reference n k) ≤ energy p f := by
  let F : Spin n→ℝ := fun x => ∑i,(f x-cond p i f x)^2
  have hle : (∫h:History n k,density p t h*energy (posterior p t h) f ∂reference n k) ≤
      ∫h:History n k,density p t h*avg (posterior p t h) F ∂reference n k := by
    apply integral_mono (integrable_posterior_energy_weight p hp t k f)
      (integrable_posterior_avg_weight p t F k)
    intro h
    exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t h f) (density_pos p t h).le
  rw [integral_posterior_avg_weight p ht] at hle
  change _≤avg p (fun x => ∑i,(f x-cond p i f x)^2) at hle
  rw [avg_sum] at hle
  exact hle

lemma squarePrior_density (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2))
    (t : ℝ) {k : ℕ} (h : History n k) :
    density (squarePrior p f hf) t h =
      density p t h*avg (posterior p t h) (fun x => (f x)^2)/avg p (fun x => (f x)^2) := by
  rw [posterior_avg_weight]
  unfold density squarePrior
  dsimp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma posterior_square_pos (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2))
    (t : ℝ) {k : ℕ} (h : History n k) : 0<avg (posterior p t h) (fun x => (f x)^2) := by
  have hs:=density_pos (squarePrior p f hf) t h
  rw [squarePrior_density] at hs
  exact (mul_pos_iff_of_pos_left (density_pos p t h)).mp ((div_pos_iff_of_pos_right hf).mp hs)

lemma squarePrior_posterior (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2))
    (t : ℝ) {k : ℕ} (h : History n k) :
    posterior (squarePrior p f hf) t h =
      squarePrior (posterior p t h) f (posterior_square_pos p f hf t h) := by
  apply Prior.ext
  funext x
  change (p x*(f x)^2/avg p (fun x => (f x)^2))*likelihood t x h /
      density (squarePrior p f hf) t h =
    (p x*likelihood t x h/density p t h)*(f x)^2/avg (posterior p t h) (fun x => (f x)^2)
  rw [squarePrior_density]
  field_simp [hf.ne', (density_pos p t h).ne', (posterior_square_pos p f hf t h).ne']

lemma weighted_energy_identity (p : Prior n) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) (t : ℝ) {k : ℕ} (h : History n k) :
    density (squarePrior p f hf) t h*
      (energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)) =
        density p t h*energy (posterior p t h) f/avg p (fun x => (f x)^2) := by
  rw [squarePrior_density]
  field_simp [(posterior_square_pos p f hf t h).ne']

lemma mean_difference_square_le (p q : Prior n) :
    (∑i,(mean q i-mean p i)^2)≤4*(n:ℝ) := by
  calc
    _≤∑i:Fin n,(4:ℝ) := Finset.sum_le_sum (fun i _ => by
      have hp:=abs_le.mp (mean_abs_le_one p i)
      have hq:=abs_le.mp (mean_abs_le_one q i)
      nlinarith [sq_nonneg (mean q i-mean p i)])
    _=_ := by simp; ring

end
end SKGap.GaussianHistory

end OAI
