import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-!
# Products of nested conditional-average factors

Finite measurable partitions model the nested mesh inside one fixed root cell.
Each factor is constant on the next partition and has average at most one on
every current cell. The product estimate below is an actual integral estimate.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

/-- Decompose a finite-profile multiplier over its measurable cells. -/
theorem integral_finite_profile_mul (μ : Measure α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) (f : α → ℝ)
    (hf : Integrable f μ) :
    (∫ x, c (P x) * f x ∂μ) = ∑ i, c i * ∫ x in {x | P x = i}, f x ∂μ := by
  classical
  have hpoint (x : α) : c (P x) * f x =
      ∑ i, c i * ({y | P y = i}.indicator f) x := by
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      simp [Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm)]
    · simp
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_indicator (hP i)]
  · intro i _
    exact (hf.indicator (hP i)).const_mul _

theorem integral_finite_profile (μ : Measure α) [IsFiniteMeasure μ]
    (P : α → κ) (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    (∫ x, c (P x) ∂μ) = ∑ i, c i * μ.real {x | P x = i} := by
  simpa only [mul_one, integral_const, smul_eq_mul, one_mul, measureReal_restrict_apply_univ] using
    integral_finite_profile_mul μ P hP c (fun _ => 1) (integrable_const 1)

theorem integrable_finite_profile (μ : Measure α) [IsFiniteMeasure μ]
    (P : α → κ) (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    Integrable (fun x => c (P x)) μ := by
  classical
  have heq : (fun x => c (P x)) =
      fun x => ∑ i, ({y | P y = i}.indicator (fun _ => c i)) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      exact Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm) _
    · simp
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (integrable_const _).indicator (hP i)

/-- Conditional cell-average domination contracts the integral of each
nonnegative factor constant on the coarse partition. -/
theorem integral_profile_mul_le (μ : Measure α) [IsFiniteMeasure μ]
    (P : α → κ) (hP : ∀ i, MeasurableSet {x | P x = i})
    (c : κ → ℝ) (hc : ∀ i, 0 ≤ c i) (f : α → ℝ) (hf : Integrable f μ)
    (haverage : ∀ i, (∫ x in {x | P x = i}, f x ∂μ) ≤ μ.real {x | P x = i}) :
    (∫ x, c (P x) * f x ∂μ) ≤ ∫ x, c (P x) ∂μ := by
  rw [integral_finite_profile_mul μ P hP c f hf, integral_finite_profile μ P hP c]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (haverage i) (hc i)

/-- The accumulated factor viewed as a function on its current partition. -/
def nestedProductProfile (R : ℕ → κ → κ) (g : ℕ → κ → ℝ) : ℕ → κ → ℝ
  | 0, _ => 1
  | n + 1, i => nestedProductProfile R g n (R n i) * g n i

omit [MeasurableSpace α] [Fintype κ] in
theorem nestedProductProfile_nonnegative (R : ℕ → κ → κ) (g : ℕ → κ → ℝ)
    {N : ℕ} (hg : ∀ n < N, ∀ i, 0 ≤ g n i) :
    ∀ n ≤ N, ∀ i, 0 ≤ nestedProductProfile R g n i := by
  intro n hn
  induction n with
  | zero => intro i; exact zero_le_one
  | succ n ih =>
    intro i
    exact mul_nonneg (ih (Nat.le_of_succ_le hn) (R n i))
      (hg n (Nat.lt_of_succ_le hn) i)

omit [MeasurableSpace α] [Fintype κ] in
theorem nestedProductProfile_eq_product (P : ℕ → α → κ) (R : ℕ → κ → κ)
    (g : ℕ → κ → ℝ) {N : ℕ}
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x)) :
    ∀ n ≤ N, ∀ x, nestedProductProfile R g n (P n x) =
      ∏ j ∈ Finset.range n, g j (P (j + 1) x) := by
  intro n hn
  induction n with
  | zero => intro x; simp [nestedProductProfile]
  | succ n ih =>
    intro x
    rw [nestedProductProfile, ← hrefine n (Nat.lt_of_succ_le hn) x,
      ih (Nat.le_of_succ_le hn) x, Finset.prod_range_succ]

theorem integrable_nested_product (μ : Measure α) [IsFiniteMeasure μ]
    (P : ℕ → α → κ) (R : ℕ → κ → κ) (g : ℕ → κ → ℝ) (N : ℕ)
    (hP : ∀ i, MeasurableSet {x | P N x = i})
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x)) :
    Integrable (fun x => ∏ j ∈ Finset.range N, g j (P (j + 1) x)) μ := by
  have heq : (fun x => ∏ j ∈ Finset.range N, g j (P (j + 1) x)) =
      fun x => nestedProductProfile R g N (P N x) := by
    funext x
    exact (nestedProductProfile_eq_product P R g hrefine N le_rfl x).symm
  rw [heq]
  exact integrable_finite_profile μ (P N) hP (nestedProductProfile R g N)

/-- Products of nonnegative next-step factors with conditional cell averages
at most one have total integral at most the measure of the root space. -/
theorem nested_average_product_le (μ : Measure α) [IsFiniteMeasure μ]
    (P : ℕ → α → κ) (R : ℕ → κ → κ) (g : ℕ → κ → ℝ) (N : ℕ)
    (hP : ∀ n ≤ N, ∀ i, MeasurableSet {x | P n x = i})
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x))
    (hg : ∀ n < N, ∀ i, 0 ≤ g n i)
    (haverage : ∀ n < N, ∀ i,
      (∫ x in {x | P n x = i}, g n (P (n + 1) x) ∂μ) ≤ μ.real {x | P n x = i}) :
    (∫ x, ∏ j ∈ Finset.range N, g j (P (j + 1) x) ∂μ) ≤ μ.real Set.univ := by
  have hstep : ∀ n < N,
      (∫ x, nestedProductProfile R g (n + 1) (P (n + 1) x) ∂μ) ≤
        ∫ x, nestedProductProfile R g n (P n x) ∂μ := by
    intro n hn
    have heq : (fun x => nestedProductProfile R g (n + 1) (P (n + 1) x)) =
        fun x => nestedProductProfile R g n (P n x) * g n (P (n + 1) x) := by
      funext x
      rw [nestedProductProfile, ← hrefine n hn x]
    rw [heq]
    exact integral_profile_mul_le μ (P n) (hP n hn.le) (nestedProductProfile R g n)
      (nestedProductProfile_nonnegative R g hg n hn.le)
      (fun x => g n (P (n + 1) x))
      (integrable_finite_profile μ (P (n + 1)) (hP (n + 1) (Nat.succ_le_of_lt hn)) (g n))
      (haverage n hn)
  have hbound : ∀ n ≤ N,
      (∫ x, nestedProductProfile R g n (P n x) ∂μ) ≤ μ.real Set.univ := by
    intro n hn
    induction n with
    | zero => simp [nestedProductProfile, integral_const]
    | succ n ih => exact (hstep n (Nat.lt_of_succ_le hn)).trans (ih (Nat.le_of_succ_le hn))
  simpa only [nestedProductProfile_eq_product P R g hrefine N le_rfl] using hbound N le_rfl

theorem nested_average_product_le_one (μ : Measure α) [IsProbabilityMeasure μ]
    (P : ℕ → α → κ) (R : ℕ → κ → κ) (g : ℕ → κ → ℝ) (N : ℕ)
    (hP : ∀ n ≤ N, ∀ i, MeasurableSet {x | P n x = i})
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x))
    (hg : ∀ n < N, ∀ i, 0 ≤ g n i)
    (haverage : ∀ n < N, ∀ i,
      (∫ x in {x | P n x = i}, g n (P (n + 1) x) ∂μ) ≤ μ.real {x | P n x = i}) :
    (∫ x, ∏ j ∈ Finset.range N, g j (P (j + 1) x) ∂μ) ≤ 1 := by
  simpa only [probReal_univ] using nested_average_product_le μ P R g N hP hrefine hg haverage

end LipschitzHilbert

end

end OAI
