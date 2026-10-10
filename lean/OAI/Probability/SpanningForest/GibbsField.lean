import OAI.Probability.SpanningForest.ExponentialFamily

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336
namespace GibbsField

variable {α ι : Type*} [Fintype α] [Fintype ι]

def weight (x : α → ι → ℝ) (h : ι → ℝ) (a : α) : ℝ :=
  Real.exp (∑ j, h j * x a j)

def mean (x : α → ι → ℝ) (a : α → ℝ) (h : ι → ℝ) : ℝ :=
  (∑ i, weight x h i * a i) / ∑ i, weight x h i

def directionValue (x : α → ι → ℝ) (k : ι → ℝ) (a : α) : ℝ :=
  ∑ j, k j * x a j

omit [Fintype α] in
theorem weight_pos (x : α → ι → ℝ) (h : ι → ℝ) (i : α) :
    0 < weight x h i := Real.exp_pos _

omit [Fintype α] in
theorem weight_shift (x : α → ι → ℝ) (h k : ι → ℝ) (i : α) (t : ℝ) :
    weight x (fun j => h j + t * k j) i =
      weight x h i * Real.exp (t * directionValue x k i) := by
  simp [weight, directionValue, add_mul, mul_assoc, Finset.sum_add_distrib,
    Finset.mul_sum, Real.exp_add]

theorem mean_shift_eq (x : α → ι → ℝ) (a : α → ℝ) (h k : ι → ℝ) (t : ℝ) :
    mean x a (fun j => h j + t * k j) =
      ExponentialFamily.mean (weight x h) (directionValue x k) a t := by
  simp only [mean, weight_shift, ExponentialFamily.mean, ExponentialFamily.numerator, ExponentialFamily.partition]

theorem hasDerivAt_mean_direction [Nonempty α]
    (x : α → ι → ℝ) (a : α → ℝ) (h k : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => mean x a (fun j => h j + s * k j))
      (mean x (fun i => a i * directionValue x k i) (fun j => h j + t * k j) -
        mean x a (fun j => h j + t * k j) *
          mean x (directionValue x k) (fun j => h j + t * k j)) t := by
  have hpos : ∃ i, 0 < weight x h i := ⟨Classical.choice ‹Nonempty α›, weight_pos x h _⟩
  simpa only [mean_shift_eq] using
    (ExponentialFamily.hasDerivAt_mean_of_nonneg (weight x h) (directionValue x k) a
      t (fun i => (weight_pos x h i).le) hpos)

def covariance (x : α → ι → ℝ) (a b : α → ℝ) (h : ι → ℝ) : ℝ :=
  mean x (fun i => a i * b i) h - mean x a h * mean x b h

theorem mean_sum {κ : Type*} [Fintype κ]
    (x : α → ι → ℝ) (f : κ → α → ℝ) (h : ι → ℝ) :
    mean x (fun i => ∑ j, f j i) h = ∑ j, mean x (f j) h := by
  simp only [mean, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]

theorem mean_const_mul (x : α → ι → ℝ) (a : α → ℝ) (h : ι → ℝ) (c : ℝ) :
    mean x (fun i => c * a i) h = c * mean x a h := by
  simp only [mean]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem covariance_direction (x : α → ι → ℝ) (a : α → ℝ) (h k : ι → ℝ) :
    covariance x a (directionValue x k) h =
      ∑ j, k j * covariance x a (fun i => x i j) h := by
  unfold covariance directionValue
  simp only [Finset.mul_sum, mean_sum]
  have hm : (fun j => mean x (fun i => a i * (k j * x i j)) h) =
      (fun j => k j * mean x (fun i => a i * x i j) h) := by
    funext j
    rw [← mean_const_mul]
    congr 1
    funext i
    ring
  rw [hm]
  simp only [mean_const_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hasDerivAt_mean_direction_sum [Nonempty α]
    (x : α → ι → ℝ) (a : α → ℝ) (h k : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => mean x a (fun j => h j + s * k j))
      (∑ j, k j * covariance x a (fun i => x i j) (fun j => h j + t * k j)) t := by
  exact (hasDerivAt_mean_direction x a h k t).congr_deriv
    (covariance_direction x a (fun j => h j + t * k j) k)

theorem hasDerivAt_mean_coordinate [Nonempty α] [DecidableEq ι]
    (x : α → ι → ℝ) (a : α → ℝ) (h : ι → ℝ) (e : ι) :
    HasDerivAt (fun t => mean x a (Function.update h e (h e + t)))
      (covariance x a (fun i => x i e) h) 0 := by
  classical
  let k : ι → ℝ := fun j => if j = e then 1 else 0
  have hk : directionValue x k = fun i => x i e := by
    funext i
    simp [directionValue, k]
  have hp : (fun t => mean x a (Function.update h e (h e + t))) =
      (fun t => mean x a (fun j => h j + t * k j)) := by
    funext t
    congr 1
    funext j
    by_cases hj : j = e <;> simp [k, hj]
  rw [hp]
  simpa only [zero_mul, add_zero, hk, covariance] using
    (hasDerivAt_mean_direction x a h k 0)

theorem partition_pos [Nonempty α] (x : α → ι → ℝ) (h : ι → ℝ) :
    0 < ∑ i, weight x h i := by
  apply Finset.sum_pos'
  · exact fun i _ => (weight_pos x h i).le
  · exact ⟨Classical.choice ‹Nonempty α›, Finset.mem_univ _, weight_pos x h _⟩

omit [Fintype α] in
@[fun_prop]
theorem continuous_weight (x : α → ι → ℝ) (i : α) :
    Continuous (fun h => weight x h i) := by
  unfold weight
  fun_prop

theorem continuous_mean [Nonempty α] (x : α → ι → ℝ) (a : α → ℝ) :
    Continuous (mean x a) := by
  unfold mean
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro h
    exact ne_of_gt (partition_pos x h)

theorem measurable_mean [Nonempty α] (x : α → ι → ℝ) (a : α → ℝ) :
    Measurable (mean x a) := (continuous_mean x a).measurable

def mass (x : α → ι → ℝ) (h : ι → ℝ) (i : α) : ℝ :=
  weight x h i / ∑ j, weight x h j

theorem mass_nonneg (x : α → ι → ℝ) (h : ι → ℝ) (i : α) :
    0 ≤ mass x h i := by
  exact div_nonneg (weight_pos x h i).le
    (Finset.sum_nonneg fun j _ => (weight_pos x h j).le)

theorem sum_mass [Nonempty α] (x : α → ι → ℝ) (h : ι → ℝ) :
    ∑ i, mass x h i = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos x h))

theorem mean_eq_sum_mass (x : α → ι → ℝ) (a : α → ℝ) (h : ι → ℝ) :
    mean x a h = ∑ i, mass x h i * a i := by
  simp only [mean, mass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end GibbsField
end Problem336

end

end OAI
