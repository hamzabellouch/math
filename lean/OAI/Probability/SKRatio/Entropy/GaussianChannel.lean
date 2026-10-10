import Mathlib
import OAI.Probability.SKRatio.FiniteChain.EntropicCovariance

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation.Channel
variable {α : Type*} [Fintype α] {d : ℕ}

def reference (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance reference_probability (d : ℕ) : IsProbabilityMeasure (reference d) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

lemma integrable_exp_linear (a : Fin d → ℝ) :
    Integrable (fun z => exp (∑ i, a i*z i)) (reference d) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a i))

lemma integral_exp_linear (a : Fin d → ℝ) :
    (∫ z, exp (∑ i, a i*z i) ∂reference d) = exp ((∑ i, a i^2)/2) := by
  simp_rw [exp_sum]
  rw [reference, integral_fintype_prod_eq_prod (fun i (z : ℝ) => exp (a i*z))]
  have hi (i : Fin d) : (∫ z : ℝ, exp (a i*z) ∂gaussianReal 0 1) = exp (a i^2/2) := by
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add,id_eq] using
      mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1) (by simp) (a i)
  simp_rw [hi]
  rw [← exp_sum,Finset.sum_div]

variable (v : α → Fin d → ℝ)

def normSq (x : α) : ℝ := ∑ i, v x i^2

def mean (p : Prior α) (i : Fin d) : ℝ := avg p (fun x => v x i)

def secondMoment (p : Prior α) : ℝ := avg p (normSq v)

def likelihood (t : ℝ) (x : α) (z : Fin d → ℝ) : ℝ :=
  exp (sqrt t*(∑ i, v x i*z i)-t*normSq v x/2)

def density (p : Prior α) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  ∑ x, p x*likelihood v t x z

omit [Fintype α] in
lemma likelihood_pos (t : ℝ) (x : α) (z : Fin d → ℝ) :
    0 < likelihood v t x z := exp_pos _

omit [Fintype α] in
lemma integrable_likelihood (t : ℝ) (x : α) :
    Integrable (likelihood v t x) (reference d) := by
  have he : likelihood v t x = fun z => exp (∑ i, (sqrt t*v x i)*z i) *
      exp (-(t*normSq v x/2)) := by
    funext z
    simp only [likelihood,exp_sub,exp_neg,← Finset.mul_sum,mul_assoc,div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

omit [Fintype α] in
lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : α) :
    (∫ z, likelihood v t x z ∂reference d) = 1 := by
  have he : likelihood v t x = fun z => exp (∑ i, (sqrt t*v x i)*z i) *
      exp (-(t*normSq v x/2)) := by
    funext z
    simp only [likelihood,exp_sub,exp_neg,← Finset.mul_sum,mul_assoc,div_eq_mul_inv]
  rw [he,integral_mul_const,integral_exp_linear,← exp_add]
  simp only [mul_pow,sq_sqrt ht,← Finset.mul_sum,normSq]
  simp

lemma density_jensen (p : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    exp (sqrt t*(∑ i, mean v p i*z i)-t*secondMoment v p/2) ≤ density v p t z := by
  have he : (∑ x, p x*(sqrt t*(∑ i, v x i*z i)-t*normSq v x/2)) =
      sqrt t*(∑ i, mean v p i*z i)-t*secondMoment v p/2 := by
    simp only [mul_sub,Finset.sum_sub_distrib,mean,secondMoment,avg,FiniteLaw.mean]
    congr 1
    · simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun x _ => by ring))
    · simp only [Finset.mul_sum,Finset.sum_div]
      exact Finset.sum_congr rfl (fun x _ => by ring)
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p.mass)
    (p := fun x => sqrt t*(∑ i, v x i*z i)-t*normSq v x/2)
    (fun x _ => p.nonneg x) p.sum_one (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul,he,density,likelihood] using hj

lemma density_pos (p : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    0 < density v p t z := (exp_pos _).trans_le (density_jensen v p t z)

lemma integrable_density (p : Prior α) (t : ℝ) :
    Integrable (density v p t) (reference d) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul (p x))

lemma integral_density (p : Prior α) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density v p t z ∂reference d) = 1 := by
  unfold density
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul (p x))]
  simp_rw [integral_const_mul,integral_likelihood v ht,mul_one]
  exact p.sum_one

def interaction (p : Prior α) (x y : α) : ℝ :=
  ((∑ i, (v x i+v y i-mean v p i)^2)-normSq v x-normSq v y+secondMoment v p)/2

lemma interaction_sum (p : Prior α) (x y : α) :
    interaction v p x y = ∑ i, (v x i*v y i-v x i*mean v p i-v y i*mean v p i+
      (mean v p i)^2/2+avg p (fun z => v z i^2)/2) := by
  have he : secondMoment v p = ∑ i, avg p (fun z => v z i^2) := by
    simp only [secondMoment,avg,FiniteLaw.mean,normSq,Finset.mul_sum]
    exact Finset.sum_comm
  rw [interaction,normSq,normSq,he,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib,Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by ring)

omit v in
lemma signed_sum_left (a u : α → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*u x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  calc
    _ = (a x*u x)*∑ y, a y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    _ = 0 := by rw [ha,mul_zero]

omit v in
lemma signed_sum_right (a u : α → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*u y) = 0 := by
  rw [Finset.sum_comm]
  convert signed_sum_left a u ha using 1
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

omit v in
lemma signed_sum_product (a u : α → ℝ) :
    (∑ x, ∑ y, a x*a y*(u x*u y)) = (∑ x, a x*u x)^2 := by
  rw [pow_two,Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))

lemma signed_interaction (p : Prior α) (a : α → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*interaction v p x y) = ∑ i, (∑ x, a x*v x i)^2 := by
  simp_rw [interaction_sum,Finset.mul_sum]
  calc
    _ = ∑ x, ∑ i, ∑ y, a x*a y*(v x i*v y i-v x i*mean v p i-v y i*mean v p i+
      (mean v p i)^2/2+avg p (fun z => v z i^2)/2) := by
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = ∑ i, ∑ x, ∑ y, a x*a y*(v x i*v y i-v x i*mean v p i-v y i*mean v p i+
      (mean v p i)^2/2+avg p (fun z => v z i^2)/2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      rw [signed_sum_product a (fun x => v x i),
        signed_sum_left a (fun x => v x i*mean v p i) ha,
        signed_sum_right a (fun x => v x i*mean v p i) ha,
        signed_sum_left a (fun _ => (mean v p i)^2/2) ha,
        signed_sum_left a (fun _ => avg p (fun z => v z i^2)/2) ha]
      ring

lemma interaction_remainder_bound (p : Prior α) {K t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) (x y : α) :
    |exp (t*interaction v p x y)-1-t*interaction v p x y| ≤ K^2*t^2 := by
  have htb : |t*interaction v p x y| ≤ K*t := by
    rw [abs_mul,abs_of_nonneg ht,mul_comm K]
    exact mul_le_mul_of_nonneg_left (hbound x y) ht
  apply (abs_exp_sub_one_sub_id_le (htb.trans hKt)).trans
  have hs := (sq_le_sq₀ (abs_nonneg (t*interaction v p x y)) (mul_nonneg hK ht)).mpr htb
  simpa only [sq_abs,mul_pow] using hs

def pairShift (p : Prior α) (x y : α) : ℝ :=
  (normSq v x+normSq v y-secondMoment v p)/2

def pairKernel (p : Prior α) (t : ℝ) (x y : α) (z : Fin d → ℝ) : ℝ :=
  exp ((∑ i, (sqrt t*(v x i+v y i-mean v p i))*z i)-t*pairShift v p x y)

lemma integrable_pairKernel (p : Prior α) (t : ℝ) (x y : α) :
    Integrable (pairKernel v p t x y) (reference d) := by
  have he : pairKernel v p t x y = fun z =>
      exp (∑ i, (sqrt t*(v x i+v y i-mean v p i))*z i)*exp (-(t*pairShift v p x y)) := by
    funext z; simp [pairKernel,exp_sub,exp_neg,div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_pairKernel (p : Prior α) {t : ℝ} (ht : 0 ≤ t) (x y : α) :
    (∫ z, pairKernel v p t x y z ∂reference d) = exp (t*interaction v p x y) := by
  have he : pairKernel v p t x y = fun z =>
      exp (∑ i, (sqrt t*(v x i+v y i-mean v p i))*z i)*exp (-(t*pairShift v p x y)) := by
    funext z; simp [pairKernel,exp_sub,exp_neg,div_eq_mul_inv]
  rw [he,integral_mul_const,integral_exp_linear,← exp_add]
  congr 1
  simp only [mul_pow,sq_sqrt ht,← Finset.mul_sum,interaction,pairShift]
  ring

lemma likelihood_pair (p : Prior α) (t : ℝ) (x y : α) (z : Fin d → ℝ) :
    likelihood v t x z * likelihood v t y z *
      exp (-(sqrt t * (∑ i, mean v p i * z i) - t*secondMoment v p/2)) = pairKernel v p t x y z := by
  unfold likelihood pairKernel pairShift
  rw [← exp_add, ← exp_add]
  congr 1
  simp only [add_mul, sub_mul, mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  ring

def majorant (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  (∑ x, a x*likelihood v t x z)^2 * exp (-(sqrt t * (∑ i, mean v p i * z i) - t*secondMoment v p/2))

lemma majorant_eq_sum (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    majorant v p a t z = ∑ x, ∑ y, (a x*a y)*pairKernel v p t x y z := by
  unfold majorant
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (a x*a y)*(likelihood v t x z*likelihood v t y z*
        exp (-(sqrt t * (∑ i, mean v p i * z i) - t*secondMoment v p/2))) := by ring
    _ = _ := by rw [likelihood_pair]

lemma majorant_nonneg (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    0 ≤ majorant v p a t z := mul_nonneg (sq_nonneg _) (exp_pos _).le

lemma integrable_majorant (p : Prior α) (a : α → ℝ) (t : ℝ) :
    Integrable (majorant v p a t) (reference d) := by
  simp_rw [show majorant v p a t = fun z => ∑ x, ∑ y, (a x*a y)*pairKernel v p t x y z from
    funext (majorant_eq_sum v p a t)]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel v p t x y).const_mul _))

lemma integral_majorant (p : Prior α) (a : α → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, majorant v p a t z ∂reference d) = ∑ x, ∑ y, (a x*a y)*exp (t*interaction v p x y) := by
  simp_rw [majorant_eq_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel v p t x y).const_mul _))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => (integrable_pairKernel v p t x y).const_mul _)]
  simp_rw [integral_const_mul, integral_pairKernel v p ht]

lemma interaction_exp_sum_bound (p : Prior α) (a : α → ℝ)
    (ha : ∑ x, a x = 0) {K t : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) :
    (∑ x, ∑ y, a x*a y*exp (t*interaction v p x y)) ≤
      t*(∑ i, (∑ x, a x*v x i)^2) +
        K^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∑ x, ∑ y, ((a x*a y + t*(a x*a y*interaction v p x y)) +
        (K^2*t^2)*(|a x| * |a y|)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hr := interaction_remainder_bound v p hK ht hbound hKt x y
      have hb : a x*a y*(exp (t*interaction v p x y)-1-t*interaction v p x y) ≤
          |a x| * |a y| * (K^2*t^2) := by
        calc
          _ ≤ |a x*a y*(exp (t*interaction v p x y)-1-t*interaction v p x y)| := le_abs_self _
          _ = |a x| * |a y| * |exp (t*interaction v p x y)-1-t*interaction v p x y| := by simp [abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      nlinarith only [hb]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [ha, signed_interaction v p a ha]
      simp only [mul_zero, Finset.sum_const_zero, zero_add, ← Finset.sum_mul]
      ring

def quadraticIntegrand (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  (∑ x, a x*likelihood v t x z)^2 / density v p t z

lemma quadraticIntegrand_nonneg (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    0 ≤ quadraticIntegrand v p a t z := div_nonneg (sq_nonneg _) (density_pos v p t z).le

lemma quadraticIntegrand_le_majorant (p : Prior α) (a : α → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    quadraticIntegrand v p a t z ≤ majorant v p a t z := by
  unfold quadraticIntegrand
  calc
    _ ≤ (∑ x, a x*likelihood v t x z)^2 /
        exp (sqrt t * (∑ i, mean v p i*z i) - t*secondMoment v p/2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (exp_pos _) (density_jensen v p t z)
    _ = _ := by simp only [majorant, div_eq_mul_inv, exp_neg]

omit [Fintype α] in
lemma continuous_likelihood (t : ℝ) (x : α) : Continuous (likelihood v t x) := by
  unfold likelihood
  fun_prop

lemma continuous_density (p : Prior α) (t : ℝ) : Continuous (density v p t) := by
  unfold density
  exact continuous_finsetSum _ (fun x _ => (continuous_likelihood v t x).const_mul _)

lemma continuous_quadraticIntegrand (p : Prior α) (a : α → ℝ) (t : ℝ) :
    Continuous (quadraticIntegrand v p a t) := by
  apply Continuous.div
    ((continuous_finsetSum _ (fun x _ => (continuous_likelihood v t x).const_mul (a x))).pow 2)
    (continuous_density v p t)
  intro z
  exact (density_pos v p t z).ne'

lemma integrable_quadraticIntegrand (p : Prior α) (a : α → ℝ) (t : ℝ) :
    Integrable (quadraticIntegrand v p a t) (reference d) := by
  apply (integrable_majorant v p a t).mono' (continuous_quadraticIntegrand v p a t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticIntegrand_nonneg v p a t z)]
  exact quadraticIntegrand_le_majorant v p a t z

theorem quadratic_bound (p : Prior α) (a : α → ℝ) (ha : ∑ x, a x = 0)
    {K t : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) :
    (∫ z, quadraticIntegrand v p a t z ∂reference d) ≤
      t*(∑ i, (∑ x, a x*v x i)^2) +
        K^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∫ z, majorant v p a t z ∂reference d :=
      integral_mono (integrable_quadraticIntegrand v p a t) (integrable_majorant v p a t)
        (quadraticIntegrand_le_majorant v p a t)
    _ = _ := integral_majorant v p a ht
    _ ≤ _ := interaction_exp_sum_bound v p a ha ht hK hbound hKt

def posterior (p : Prior α) (t : ℝ) (z : Fin d → ℝ) : Prior α where
  mass x := p x * likelihood v t x z / density v p t z
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos v t x z).le)
    (density_pos v p t z).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (density_pos v p t z).ne'

lemma posterior_avg_weight (p : Prior α) (t : ℝ) (z : Fin d → ℝ) (f : α → ℝ) :
    density v p t z * avg (posterior v p t z) f = ∑ x, (p x*f x)*likelihood v t x z := by
  unfold avg FiniteLaw.mean posterior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp
  field_simp [(density_pos v p t z).ne']

lemma integrable_posterior_avg_weight (p : Prior α) (t : ℝ) (f : α → ℝ) :
    Integrable (fun z => density v p t z * avg (posterior v p t z) f) (reference d) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul _)

lemma integral_posterior_avg_weight (p : Prior α) {t : ℝ} (ht : 0 ≤ t) (f : α → ℝ) :
    (∫ z, density v p t z * avg (posterior v p t z) f ∂reference d) = avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood v t x).const_mul _)]
  simp_rw [integral_const_mul, integral_likelihood v ht, mul_one]
  rfl

lemma scalar_entropy_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ r*log r-r+1 := by
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hr) hr.le
  have hi : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith

lemma scalar_entropy_le_square {r : ℝ} (hr : 0 < r) : r*log r-r+1 ≤ (r-1)^2 := by
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hr) hr.le
  nlinarith

def divergenceIntegrand (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  density v q t z * log (density v q t z/density v p t z) - density v q t z + density v p t z

lemma divergenceIntegrand_eq (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    divergenceIntegrand v p q t z = density v p t z *
      ((density v q t z/density v p t z)*log (density v q t z/density v p t z)-
        density v q t z/density v p t z+1) := by
  unfold divergenceIntegrand
  field_simp [(density_pos v p t z).ne']

lemma divergenceIntegrand_nonneg (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    0 ≤ divergenceIntegrand v p q t z := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos v p t z).le
    (scalar_entropy_nonneg (div_pos (density_pos v q t z) (density_pos v p t z)))

lemma density_sub (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    (∑ x, (q x-p x)*likelihood v t x z) = density v q t z-density v p t z := by
  simp only [sub_mul, Finset.sum_sub_distrib, density]

lemma divergenceIntegrand_le_quadratic (p q : Prior α) (t : ℝ) (z : Fin d → ℝ) :
    divergenceIntegrand v p q t z ≤ quadraticIntegrand v p (fun x => q x-p x) t z := by
  rw [divergenceIntegrand_eq, quadraticIntegrand, density_sub]
  calc
    _ ≤ density v p t z*(density v q t z/density v p t z-1)^2 :=
      mul_le_mul_of_nonneg_left
        (scalar_entropy_le_square (div_pos (density_pos v q t z) (density_pos v p t z)))
        (density_pos v p t z).le
    _ = _ := by field_simp [(density_pos v p t z).ne']

lemma continuous_divergenceIntegrand (p q : Prior α) (t : ℝ) :
    Continuous (divergenceIntegrand v p q t) := by
  have hd := (continuous_density v q t).div (continuous_density v p t)
    (fun z => (density_pos v p t z).ne')
  exact (((continuous_density v q t).mul (hd.log (fun z =>
    (div_pos (density_pos v q t z) (density_pos v p t z)).ne'))).sub
      (continuous_density v q t)).add (continuous_density v p t)

lemma integrable_divergenceIntegrand (p q : Prior α) (t : ℝ) :
    Integrable (divergenceIntegrand v p q t) (reference d) := by
  apply (integrable_quadraticIntegrand v p (fun x => q x-p x) t).mono'
    (continuous_divergenceIntegrand v p q t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (divergenceIntegrand_nonneg v p q t z)]
  exact divergenceIntegrand_le_quadratic v p q t z

lemma prior_sub_l1 (p q : Prior α) : (∑ x, |q x-p x|) ≤ 2 := by
  calc
    _ ≤ ∑ x, (q x+p x) := Finset.sum_le_sum (fun x _ => by
      simpa only [abs_of_nonneg (q.nonneg x), abs_of_nonneg (p.nonneg x)] using abs_sub (q x) (p x))
    _ = 2 := by rw [Finset.sum_add_distrib, q.sum_one, p.sum_one]; norm_num

lemma prior_sub_sum (p q : Prior α) : (∑ x, (q x-p x)) = 0 := by
  rw [Finset.sum_sub_distrib, q.sum_one, p.sum_one, sub_self]

theorem entropy_step_bound (p q : Prior α) {K t : ℝ} (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1) :
    (∫ z, divergenceIntegrand v p q t z ∂reference d) ≤
      t*(∑ i, (mean v q i-mean v p i)^2)+4*K^2*t^2 := by
  have hmean : (∑ i, (∑ x, (q x-p x)*v x i)^2) =
      ∑ i, (mean v q i-mean v p i)^2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mean, avg, FiniteLaw.mean]
  have he : (∑ x, |q x-p x|)^2 ≤ 4 := by
    have hl : 0 ≤ ∑ x, |q x-p x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    nlinarith [prior_sub_l1 p q]
  calc
    _ ≤ ∫ z, quadraticIntegrand v p (fun x => q x-p x) t z ∂reference d :=
      integral_mono (integrable_divergenceIntegrand v p q t) (integrable_quadraticIntegrand v p _ t)
        (divergenceIntegrand_le_quadratic v p q t)
    _ ≤ t*(∑ i, (mean v q i-mean v p i)^2)+K^2*t^2*(∑ x, |q x-p x|)^2 := by
      simpa only [hmean] using quadratic_bound v p (fun x => q x-p x) (prior_sub_sum p q) ht hK hbound hKt
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ K^2*t^2 by positivity)]

lemma integrable_relativeEntropy (p q : Prior α) (t : ℝ) :
    Integrable (fun z => density v q t z*log (density v q t z/density v p t z)) (reference d) := by
  have he : (fun z => density v q t z*log (density v q t z/density v p t z)) =
      fun z => divergenceIntegrand v p q t z+density v q t z-density v p t z := by
    funext z
    unfold divergenceIntegrand
    ring
  rw [he]
  exact ((integrable_divergenceIntegrand v p q t).add (integrable_density v q t)).sub
    (integrable_density v p t)

lemma integral_relativeEntropy (p q : Prior α) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density v q t z*log (density v q t z/density v p t z) ∂reference d) =
      ∫ z, divergenceIntegrand v p q t z ∂reference d := by
  have hi := integral_add
    ((integrable_relativeEntropy v p q t).sub (integrable_density v q t)) (integrable_density v p t)
  have hj := integral_sub (integrable_relativeEntropy v p q t) (integrable_density v q t)
  simp only [Pi.sub_apply] at hi hj
  rw [hj, integral_density v q ht, integral_density v p ht] at hi
  change (∫ z, divergenceIntegrand v p q t z ∂reference d) = _ at hi
  linarith

lemma mean_abs_le (p : Prior α) {B : ℝ} (hB : ∀ x i, |v x i| ≤ B) (i : Fin d) :
    |mean v p i| ≤ B := by
  calc
    _ ≤ ∑ x, |p x*v x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, p x*B := Finset.sum_le_sum (fun x _ => by
      rw [abs_mul,abs_of_nonneg (p.nonneg x)]
      exact mul_le_mul_of_nonneg_left (hB x i) (p.nonneg x))
    _ = B := by rw [← Finset.sum_mul,p.sum_one,one_mul]

omit [Fintype α] in
lemma normSq_nonneg (x : α) : 0 ≤ normSq v x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [Fintype α] in
lemma normSq_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x i, |v x i| ≤ B) (x : α) :
    normSq v x ≤ d*B^2 := by
  calc
    _ ≤ ∑ _i : Fin d, B^2 := Finset.sum_le_sum (fun i _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB0).mpr (hB x i))
    _ = _ := by simp

lemma interaction_abs_le (p : Prior α) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x i, |v x i| ≤ B) (x y : α) :
    |interaction v p x y| ≤ 5*d*B^2 := by
  have hmean (i : Fin d) := mean_abs_le v p hB i
  have hsec : 0 ≤ secondMoment v p := avg_nonneg p (normSq_nonneg v)
  have hsecb : secondMoment v p ≤ d*B^2 := by
    exact (avg_mono p (normSq_le v hB0 hB)).trans_eq (avg_const p _)
  have hs0 : 0 ≤ ∑ i, (v x i+v y i-mean v p i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ i, (v x i+v y i-mean v p i)^2) ≤ 9*d*B^2 := by
    calc
      _ ≤ ∑ _i : Fin d, (3*B)^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hh : |v x i+v y i-mean v p i| ≤ 3*B := by
          have hh := (abs_sub (v x i+v y i) (mean v p i)).trans
            (add_le_add (abs_add_le (v x i) (v y i)) le_rfl)
          linarith [hB x i,hB y i,hmean i]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
      _ = _ := by simp;ring
  rw [abs_le]
  unfold interaction
  constructor <;> nlinarith [normSq_nonneg v x,normSq_nonneg v y,
    normSq_le v hB0 hB x,normSq_le v hB0 hB y,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (sq_nonneg B)]

theorem exists_interaction_bound : ∃ K : ℝ, 0 ≤ K ∧
    ∀ p : Prior α, ∀ x y, |interaction v p x y| ≤ K := by
  let B := ∑ x, ∑ i, |v x i|
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hB (x : α) (i : Fin d) : |v x i| ≤ B := by
    exact (Finset.single_le_sum (f := fun j => |v x j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun y => ∑ j, |v y j|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ x))
  exact ⟨5*d*B^2,by positivity,fun p x y => interaction_abs_le v p hB0 hB x y⟩

lemma reweight_density (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (t : ℝ) (z : Fin d → ℝ) :
    density v (reweight p f hf) t z =
      density v p t z*avg (posterior v p t z) f/avg p f := by
  rw [posterior_avg_weight]
  unfold density reweight
  dsimp
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma posterior_avg_eq_density_ratio (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (t : ℝ) (z : Fin d → ℝ) :
    avg (posterior v p t z) f = avg p f*(density v (reweight p f hf) t z/density v p t z) := by
  rw [reweight_density]
  field_simp [(avg_pos p hf).ne',(density_pos v p t z).ne']

lemma posterior_entropy_identity (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (t : ℝ) (z : Fin d → ℝ) :
    density v p t z*ent (posterior v p t z) f =
      density v p t z*avg (posterior v p t z) (fun x => f x*log (f x)) -
      avg p f*(density v (reweight p f hf) t z*log (density v (reweight p f hf) t z/density v p t z)) -
      log (avg p f)*(density v p t z*avg (posterior v p t z) f) := by
  change density v p t z*(avg (posterior v p t z) (fun x => f x*log (f x))-
    avg (posterior v p t z) f*log (avg (posterior v p t z) f)) = _
  rw [posterior_avg_eq_density_ratio v p f hf,log_mul (avg_pos p hf).ne'
    (div_pos (density_pos v (reweight p f hf) t z) (density_pos v p t z)).ne']
  field_simp [(density_pos v p t z).ne']
  ring

lemma integrable_posterior_entropy_weight (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x) (t : ℝ) :
    Integrable (fun z => density v p t z*ent (posterior v p t z) f) (reference d) := by
  simp_rw [posterior_entropy_identity v p f hf]
  exact ((integrable_posterior_avg_weight v p t _).sub
    ((integrable_relativeEntropy v p (reweight p f hf) t).const_mul _)).sub
    ((integrable_posterior_avg_weight v p t f).const_mul _)

lemma integral_posterior_entropy (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density v p t z*ent (posterior v p t z) f ∂reference d) =
      ent p f-avg p f*(∫ z, divergenceIntegrand v p (reweight p f hf) t z ∂reference d) := by
  simp_rw [posterior_entropy_identity v p f hf]
  have h₁ := integrable_posterior_avg_weight v p t (fun x => f x*log (f x))
  have h₂ := (integrable_relativeEntropy v p (reweight p f hf) t).const_mul (avg p f)
  have h₃ := (integrable_posterior_avg_weight v p t f).const_mul (log (avg p f))
  have h₄ := integral_sub (h₁.sub h₂) h₃
  have h₅ := integral_sub h₁ h₂
  simp only [Pi.sub_apply] at h₄ h₅
  rw [h₄,h₅,integral_const_mul,integral_const_mul,
    integral_posterior_avg_weight v p ht,integral_posterior_avg_weight v p ht,
    integral_relativeEntropy v p (reweight p f hf) ht]
  unfold ent FiniteLaw.entropy avg
  ring

theorem entropy_retention (p : Prior α) (f : α → ℝ) (hf : ∀ x, 0 < f x)
    (hp : ∀ x, 0 < p x) {C K t : ℝ} (hC : 0 < C) (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hbound : ∀ x y, |interaction v p x y| ≤ K) (hKt : K*t ≤ 1)
    (hvar : ∀ a : Fin d → ℝ, ∀ s : ℝ,
      var (tilt p (linear v a) s) (linear v a) ≤ C*(∑ i, a i^2)) :
    (1-2*C*t)*ent p f-4*K^2*t^2*avg p f ≤
      ∫ z, density v p t z*ent (posterior v p t z) f ∂reference d := by
  have h := entropy_step_bound v p (reweight p f hf) ht hK hbound hKt
  have hd := vector_mean_displacement_sq p (reweight p f hf) v hp hC hvar
  rw [relativeEntropy_reweight p f hf hp] at hd
  change (∑ i, (mean v (reweight p f hf) i-mean v p i)^2) ≤ _ at hd
  have he := mul_le_mul_of_nonneg_left hd ht
  have hh := mul_le_mul_of_nonneg_left
    (h.trans (add_le_add he le_rfl)) (avg_pos p hf).le
  rw [integral_posterior_entropy v p f hf ht]
  have heq : avg p f*(t*(2*C*(ent p f/avg p f))+4*K^2*t^2) =
      2*C*t*ent p f+4*K^2*t^2*avg p f := by
    field_simp [(avg_pos p hf).ne']
  rw [heq] at hh
  nlinarith only [hh]

end SKRatio.Observation.Channel

end
end

end OAI
