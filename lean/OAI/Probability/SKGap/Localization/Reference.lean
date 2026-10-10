import Mathlib
import OAI.Probability.SKGap.Localization.LiteralRegularity

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

def reference (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance reference_probability (n : ℕ) : IsProbabilityMeasure (reference n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

lemma integrable_exp_linear (a : Fin n → ℝ) :
    Integrable (fun z => exp (∑ i, a i * z i)) (reference n) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a i))

lemma integral_exp_linear (a : Fin n → ℝ) :
    (∫ z, exp (∑ i, a i * z i) ∂reference n) = exp ((∑ i, (a i)^2) / 2) := by
  simp_rw [exp_sum]
  rw [reference, integral_fintype_prod_eq_prod (fun i (z : ℝ) => exp (a i*z))]
  have hi (i : Fin n) : (∫ z : ℝ, exp (a i * z) ∂gaussianReal 0 1) = exp ((a i)^2/2) := by
    simpa only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add, id_eq] using
      mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1) (by simp) (a i)
  simp_rw [hi]
  rw [← exp_sum, Finset.sum_div]

structure Prior (n : ℕ) where
  mass : Spin n → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

@[ext] lemma Prior.ext {p q : Prior n} (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  congr

instance : CoeFun (Prior n) (fun _ => Spin n → ℝ) := ⟨Prior.mass⟩

def gibbsPrior (g : Disorder n) (h : Fin n → ℝ) : Prior n :=
  ⟨mass g h, mass_nonneg g h, sum_mass g h⟩

def mean (p : Prior n) (i : Fin n) : ℝ := ∑ x, p x * spinValue (x i)

def likelihood (t : ℝ) (x : Spin n) (z : Fin n → ℝ) : ℝ :=
  exp (sqrt t * (∑ i, spinValue (x i) * z i) - t * n / 2)

def density (p : Prior n) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ x, p x * likelihood t x z

lemma likelihood_pos (t : ℝ) (x : Spin n) (z : Fin n → ℝ) :
    0 < likelihood t x z := exp_pos _

lemma integrable_likelihood (t : ℝ) (x : Spin n) :
    Integrable (likelihood t x) (reference n) := by
  have he : likelihood t x = fun z => exp (∑ i, (sqrt t * spinValue (x i)) * z i) *
      exp (-(t*n/2)) := by
    funext z
    simp only [likelihood, exp_sub, exp_neg, ← Finset.mul_sum, mul_assoc, div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : Spin n) :
    (∫ z, likelihood t x z ∂reference n) = 1 := by
  have he : likelihood t x = fun z => exp (∑ i, (sqrt t * spinValue (x i)) * z i) *
      exp (-(t*n/2)) := by
    funext z
    simp only [likelihood, exp_sub, exp_neg, ← Finset.mul_sum, mul_assoc, div_eq_mul_inv]
  rw [he, integral_mul_const, integral_exp_linear, ← exp_add]
  have hs : (∑ i, (sqrt t * spinValue (x i)) ^ 2) = t*n := by
    simp [mul_pow, sq_sqrt ht, spinValue_sq, mul_comm]
  rw [hs]
  simp

lemma density_jensen (p : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    exp (sqrt t * (∑ i, mean p i * z i) - t*n/2) ≤ density p t z := by
  have he : (∑ x, p x * (sqrt t * (∑ i, spinValue (x i) * z i) - t*n/2)) =
      sqrt t * (∑ i, mean p i * z i) - t*n/2 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, p.sum_one, one_mul]
    congr 1
    simp only [mean, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p.mass)
    (p := fun x => sqrt t * (∑ i, spinValue (x i) * z i) - t*n/2)
    (fun x _ => p.nonneg x) p.sum_one (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, he, density, likelihood] using hj

lemma density_pos (p : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    0 < density p t z := (exp_pos _).trans_le (density_jensen p t z)

lemma integrable_density (p : Prior n) (t : ℝ) :
    Integrable (density p t) (reference n) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul (p x))

lemma integral_density (p : Prior n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density p t z ∂reference n) = 1 := by
  change (∫ z, ∑ x, p x * likelihood t x z ∂reference n) = 1
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul (p x))]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  exact p.sum_one

lemma mean_abs_le_one (p : Prior n) (i : Fin n) : |mean p i| ≤ 1 := by
  calc
    |mean p i| ≤ ∑ x, |p x * spinValue (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, p x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]
      have hs : |spinValue (x i)| = 1 := by cases x i <;> norm_num [spinValue]
      rw [hs, mul_one]
    _ = 1 := p.sum_one

def interaction (p : Prior n) (x y : Spin n) : ℝ :=
  ((∑ i, (spinValue (x i) + spinValue (y i) - mean p i)^2) - n) / 2

lemma interaction_abs_le (p : Prior n) (x y : Spin n) :
    |interaction p x y| ≤ 4*n := by
  have hl : (0 : ℝ) ≤ ∑ i : Fin n, (spinValue (x i) + spinValue (y i) - mean p i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hu : (∑ i : Fin n, (spinValue (x i) + spinValue (y i) - mean p i)^2) ≤ 9*n := by
    calc
      _ ≤ ∑ _i : Fin n, (9 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hx : |spinValue (x i)| = 1 := by cases x i <;> norm_num [spinValue]
        have hy : |spinValue (y i)| = 1 := by cases y i <;> norm_num [spinValue]
        have hb : |spinValue (x i) + spinValue (y i) - mean p i| ≤ 3 := by
          calc
            _ ≤ |spinValue (x i) + spinValue (y i)| + |mean p i| := abs_sub _ _
            _ ≤ |spinValue (x i)| + |spinValue (y i)| + |mean p i| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ ≤ 3 := by rw [hx, hy]; linarith [mean_abs_le_one p i]
        have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3)).mpr hb
        simpa only [sq_abs, show (3:ℝ)^2 = 9 by norm_num] using hh
      _ = 9*n := by simp [mul_comm]
  rw [abs_le]
  unfold interaction
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma interaction_remainder_bound (p : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) (x y : Spin n) :
    |exp (t * interaction p x y) - 1 - t * interaction p x y| ≤
      16*(n:ℝ)^2*t^2 := by
  have hb := interaction_abs_le p x y
  have htb : |t * interaction p x y| ≤ 4*(n:ℝ)*t := by
    rw [abs_mul, abs_of_nonneg ht]
    nlinarith [mul_le_mul_of_nonneg_left hb ht]
  apply (abs_exp_sub_one_sub_id_le (htb.trans htn)).trans
  have hs := sq_le_sq₀ (abs_nonneg (t * interaction p x y)) (by positivity) |>.mpr htb
  simpa only [sq_abs] using (hs.trans_eq (by ring : (4*(n:ℝ)*t)^2 = 16*(n:ℝ)^2*t^2))

lemma interaction_sum (p : Prior n) (x y : Spin n) :
    interaction p x y = ∑ i, ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := by
  have ha : interaction p x y = ∑ i, ((spinValue (x i) + spinValue (y i) - mean p i)^2 - 1)/2 := by
    unfold interaction
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  rw [ha]
  apply Finset.sum_congr rfl
  intro i _
  nlinarith [spinValue_sq (x i), spinValue_sq (y i)]

lemma signed_sum_left (a u : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x * a y * u x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  calc
    _ = (a x * u x) * ∑ y, a y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = 0 := by rw [ha, mul_zero]

lemma signed_sum_right (a u : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x * a y * u y) = 0 := by
  rw [Finset.sum_comm]
  convert signed_sum_left a u ha using 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma signed_sum_product (a u : Spin n → ℝ) :
    (∑ x, ∑ y, a x * a y * (u x * u y)) = (∑ x, a x*u x)^2 := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma signed_interaction (p : Prior n) (a : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*interaction p x y) =
      ∑ i, (∑ x, a x*spinValue (x i))^2 := by
  simp_rw [interaction_sum, Finset.mul_sum]
  calc
    _ = ∑ x, ∑ i, ∑ y, a x*a y* ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, a x*a y* ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [signed_sum_left a (fun _ => (1/2 : ℝ)) ha,
        signed_sum_product a (fun x => spinValue (x i)),
        signed_sum_left a (fun x => spinValue (x i)*mean p i) ha,
        signed_sum_right a (fun y => spinValue (y i)*mean p i) ha,
        signed_sum_left a (fun _ => (mean p i)^2/2) ha]
      ring

def pairKernel (p : Prior n) (t : ℝ) (x y : Spin n) (z : Fin n → ℝ) : ℝ :=
  exp ((∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) - t*n/2)

lemma integrable_pairKernel (p : Prior n) (t : ℝ) (x y : Spin n) :
    Integrable (pairKernel p t x y) (reference n) := by
  have he : pairKernel p t x y = fun z =>
      exp (∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) *
        exp (-(t*n/2)) := by funext z; simp [pairKernel, exp_sub, exp_neg, div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_pairKernel (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (x y : Spin n) :
    (∫ z, pairKernel p t x y z ∂reference n) = exp (t*interaction p x y) := by
  have he : pairKernel p t x y = fun z =>
      exp (∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) *
        exp (-(t*n/2)) := by funext z; simp [pairKernel, exp_sub, exp_neg, div_eq_mul_inv]
  rw [he, integral_mul_const, integral_exp_linear, ← exp_add]
  congr 1
  simp only [mul_pow, sq_sqrt ht, ← Finset.mul_sum, interaction]
  ring

lemma likelihood_pair (p : Prior n) (t : ℝ) (x y : Spin n) (z : Fin n → ℝ) :
    likelihood t x z * likelihood t y z *
      exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2)) = pairKernel p t x y z := by
  unfold likelihood pairKernel
  rw [← exp_add, ← exp_add]
  congr 1
  simp only [add_mul, sub_mul, mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  ring

def majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ x, a x*likelihood t x z)^2 * exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2))

lemma majorant_eq_sum (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    majorant p a t z = ∑ x, ∑ y, (a x*a y)*pairKernel p t x y z := by
  unfold majorant
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (a x*a y)*(likelihood t x z*likelihood t y z*
        exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2))) := by ring
    _ = _ := by rw [likelihood_pair]

lemma majorant_nonneg (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    0 ≤ majorant p a t z := mul_nonneg (sq_nonneg _) (exp_pos _).le

lemma integrable_majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Integrable (majorant p a t) (reference n) := by
  simp_rw [show majorant p a t = fun z => ∑ x, ∑ y, (a x*a y)*pairKernel p t x y z from
    funext (majorant_eq_sum p a t)]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel p t x y).const_mul _))

lemma integral_majorant (p : Prior n) (a : Spin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, majorant p a t z ∂reference n) = ∑ x, ∑ y, (a x*a y)*exp (t*interaction p x y) := by
  simp_rw [majorant_eq_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel p t x y).const_mul _))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => (integrable_pairKernel p t x y).const_mul _)]
  simp_rw [integral_const_mul, integral_pairKernel p ht]

lemma interaction_exp_sum_bound (p : Prior n) (a : Spin n → ℝ)
    (ha : ∑ x, a x = 0) {t : ℝ} (ht : 0 ≤ t) (htn : 4*(n:ℝ)*t ≤ 1) :
    (∑ x, ∑ y, a x*a y*exp (t*interaction p x y)) ≤
      t*(∑ i, (∑ x, a x*spinValue (x i))^2) +
        16*(n:ℝ)^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∑ x, ∑ y, ((a x*a y + t*(a x*a y*interaction p x y)) +
        (16*(n:ℝ)^2*t^2)*(|a x| * |a y|)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hr := interaction_remainder_bound p ht htn x y
      have hb : a x*a y*(exp (t*interaction p x y)-1-t*interaction p x y) ≤
          |a x| * |a y| * (16*(n:ℝ)^2*t^2) := by
        calc
          _ ≤ |a x*a y*(exp (t*interaction p x y)-1-t*interaction p x y)| := le_abs_self _
          _ = |a x| * |a y| * |exp (t*interaction p x y)-1-t*interaction p x y| := by simp [abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      nlinarith only [hb]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [ha, signed_interaction p a ha]
      simp only [mul_zero, Finset.sum_const_zero, zero_add, ← Finset.sum_mul]
      ring

def quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ x, a x*likelihood t x z)^2 / density p t z

lemma quadraticIntegrand_nonneg (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    0 ≤ quadraticIntegrand p a t z := div_nonneg (sq_nonneg _) (density_pos p t z).le

lemma quadraticIntegrand_le_majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    quadraticIntegrand p a t z ≤ majorant p a t z := by
  unfold quadraticIntegrand
  calc
    _ ≤ (∑ x, a x*likelihood t x z)^2 /
        exp (sqrt t * (∑ i, mean p i*z i) - t*n/2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (exp_pos _) (density_jensen p t z)
    _ = _ := by simp only [majorant, div_eq_mul_inv, exp_neg]

lemma continuous_likelihood (t : ℝ) (x : Spin n) : Continuous (likelihood t x) := by
  unfold likelihood
  fun_prop

lemma continuous_density (p : Prior n) (t : ℝ) : Continuous (density p t) := by
  unfold density
  exact continuous_finsetSum _ (fun x _ => (continuous_likelihood t x).const_mul _)

lemma continuous_quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Continuous (quadraticIntegrand p a t) := by
  apply Continuous.div
    ((continuous_finsetSum _ (fun x _ => (continuous_likelihood t x).const_mul (a x))).pow 2)
    (continuous_density p t)
  intro z
  exact (density_pos p t z).ne'

lemma integrable_quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Integrable (quadraticIntegrand p a t) (reference n) := by
  apply (integrable_majorant p a t).mono' (continuous_quadraticIntegrand p a t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticIntegrand_nonneg p a t z)]
  exact quadraticIntegrand_le_majorant p a t z

theorem quadratic_bound (p : Prior n) (a : Spin n → ℝ) (ha : ∑ x, a x = 0)
    {t : ℝ} (ht : 0 ≤ t) (htn : 4*(n:ℝ)*t ≤ 1) :
    (∫ z, quadraticIntegrand p a t z ∂reference n) ≤
      t*(∑ i, (∑ x, a x*spinValue (x i))^2) +
        16*(n:ℝ)^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∫ z, majorant p a t z ∂reference n :=
      integral_mono (integrable_quadraticIntegrand p a t) (integrable_majorant p a t)
        (quadraticIntegrand_le_majorant p a t)
    _ = _ := integral_majorant p a ht
    _ ≤ _ := interaction_exp_sum_bound p a ha ht htn

def avg (p : Prior n) (f : Spin n → ℝ) : ℝ := ∑ x, p x * f x

def var (p : Prior n) (f : Spin n → ℝ) : ℝ :=
  avg p (fun x => (f x - avg p f)^2)

def posterior (p : Prior n) (t : ℝ) (z : Fin n → ℝ) : Prior n where
  mass x := p x * likelihood t x z / density p t z
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos t x z).le)
    (density_pos p t z).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (density_pos p t z).ne'

lemma var_nonneg (p : Prior n) (f : Spin n → ℝ) : 0 ≤ var p f :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (p.nonneg _) (sq_nonneg _))

lemma avg_const (p : Prior n) (c : ℝ) : avg p (fun _ => c) = c := by
  rw [avg, ← Finset.sum_mul, p.sum_one, one_mul]

lemma avg_sub (p : Prior n) (f g : Spin n → ℝ) :
    avg p (fun x => f x-g x) = avg p f-avg p g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

lemma avg_mul_const (p : Prior n) (f : Spin n → ℝ) (c : ℝ) :
    avg p (fun x => f x*c) = avg p f*c := by
  simp only [avg, mul_assoc, Finset.sum_mul]

lemma avg_center (p : Prior n) (f : Spin n → ℝ) :
    avg p (fun x => f x-avg p f) = 0 := by rw [avg_sub, avg_const, sub_self]

lemma avg_shift_square (p : Prior n) (f : Spin n → ℝ) (c : ℝ) :
    avg p (fun x => (f x-c)^2) = avg p (fun x => (f x)^2)-2*c*avg p f+c^2 := by
  unfold avg
  calc
    _ = ∑ x, ((p x*(f x)^2-(p x*f x)*(2*c))+p x*c^2) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, p.sum_one]
      ring

end
end SKGap.GaussianStep

end OAI
