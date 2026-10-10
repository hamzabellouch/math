import OAI.Algebra.DepthFive.OccupationSum
import OAI.Algebra.DepthFive.OccupationComparison

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Uniform average over all weak compositions of `t` in the coordinates `ι`. -/
def occupationAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (f : (ι →₀ ℕ) → ℝ) : ℝ :=
  (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) t, f M) /
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) t).card

lemma occupationAverage_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (s : Finset κ) (f : κ → (ι →₀ ℕ) → ℝ) :
    occupationAverage t (fun M => ∑ j ∈ s, f j M) =
      ∑ j ∈ s, occupationAverage t (f j) := by
  unfold occupationAverage
  rw [Finset.sum_comm, Finset.sum_div]

lemma occupationAverage_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (f : (ι →₀ ℕ) → ℝ) (hf : ∀ M, 0 ≤ f M) :
    0 ≤ occupationAverage t f := by
  unfold occupationAverage
  exact div_nonneg (Finset.sum_nonneg fun M _ => hf M) (Nat.cast_nonneg _)

/-- The squarefree occupation product needed by differentiated path layers. -/
theorem occupationAverage_prod {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (t : ℕ) (s : Finset ι) :
    occupationAverage t (fun M => ∏ i ∈ s, (M i : ℝ)) =
      (t.descFactorial s.card : ℝ) / ((Fintype.card ι).ascFactorial s.card : ℝ) := by
  have h := occupation_factorial_moment (fun i => if i ∈ s then 1 else 0) t
  simpa [occupationAverage, apply_ite] using h

/-- Multiplication layers supply successor occupations; expand them by subsets. -/
theorem occupationAverage_prod_add_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) :
    occupationAverage t (fun M => ∏ i ∈ s, ((M i : ℝ) + 1)) =
      ∑ z ∈ s.powerset,
        (t.descFactorial z.card : ℝ) / ((Fintype.card ι).ascFactorial z.card : ℝ) := by
  simp_rw [Finset.prod_add_one]
  rw [occupationAverage_sum]
  simp_rw [occupationAverage_prod]

lemma occupation_powerset_sum {ι : Type*} (s : Finset ι) (x : ℝ) :
    (∑ z ∈ s.powerset, x ^ z.card) = (1 + x) ^ s.card := by
  simpa using (Finset.prod_one_add (f := fun _ : ι => x) s).symm

/-- A uniform factorial-moment loss transfers to the successor product. -/
theorem occupationAverage_prod_add_one_lower_of_factorial {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (t : ℕ) (s : Finset ι) (L : ℝ)
    (hL : ∀ H ≤ s.card,
      L * ((t : ℝ) / Fintype.card ι) ^ H ≤
        (t.descFactorial H : ℝ) / ((Fintype.card ι).ascFactorial H : ℝ)) :
    L * (1 + (t : ℝ) / Fintype.card ι) ^ s.card ≤
      occupationAverage t (fun M => ∏ i ∈ s, ((M i : ℝ) + 1)) := by
  rw [occupationAverage_prod_add_one, ← occupation_powerset_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  exact hL z.card (Finset.card_le_card (Finset.mem_powerset.mp hz))

/-- Independent composition averages factor without any probabilistic
independence convention being implicit. -/
theorem occupationAverage_tensor {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (a b : ℕ)
    (f : (ι →₀ ℕ) → ℝ) (g : (κ →₀ ℕ) → ℝ) :
    (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) a,
      ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset κ) b, f M * g N) /
        ((Finset.finsuppAntidiag (Finset.univ : Finset ι) a).card *
          (Finset.finsuppAntidiag (Finset.univ : Finset κ) b).card : ℝ) =
      occupationAverage a f * occupationAverage b g := by
  unfold occupationAverage
  rw [← Finset.sum_mul_sum, mul_div_mul_comm]

theorem occupationAverage_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) :
    occupationAverage t (fun M => ∏ i ∈ s, (M i : ℝ)) ≤
      ((t : ℝ) / Fintype.card ι) ^ s.card := by
  rw [occupationAverage_prod]
  exact descFactorial_div_ascFactorial_le_mean_pow_of_pos Fintype.card_pos

theorem occupationAverage_prod_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) (ht : 0 < t) (hs : 2 * s.card ≤ t) :
    Real.exp (-(s.card : ℝ) ^ 2 / t - (s.card : ℝ) ^ 2 / (2 * Fintype.card ι)) *
      ((t : ℝ) / Fintype.card ι) ^ s.card ≤
        occupationAverage t (fun M => ∏ i ∈ s, (M i : ℝ)) := by
  rw [occupationAverage_prod]
  exact exp_mul_mean_pow_le_descFactorial_div_ascFactorial ht Fintype.card_pos hs

theorem occupationAverage_prod_add_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) :
    occupationAverage t (fun M => ∏ i ∈ s, ((M i : ℝ) + 1)) ≤
      (1 + (t : ℝ) / Fintype.card ι) ^ s.card := by
  rw [occupationAverage_prod_add_one, ← occupation_powerset_sum]
  apply Finset.sum_le_sum
  intro z hz
  exact descFactorial_div_ascFactorial_le_mean_pow_of_pos Fintype.card_pos

theorem occupationAverage_prod_add_one_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (t : ℕ) (s : Finset ι) (ht : 0 < t) (hs : 2 * s.card ≤ t) :
    Real.exp (-(s.card : ℝ) ^ 2 / t - (s.card : ℝ) ^ 2 / (2 * Fintype.card ι)) *
      (1 + (t : ℝ) / Fintype.card ι) ^ s.card ≤
        occupationAverage t (fun M => ∏ i ∈ s, ((M i : ℝ) + 1)) := by
  apply occupationAverage_prod_add_one_lower_of_factorial
  intro H hH
  exact occupation_factorial_ratio_lower_of_le ht Fintype.card_pos hH hs

/-- The two-group first-trace occupation estimate, with its exact finite-size
loss and no asymptotic or independence premises. -/
theorem occupation_first_moment_lower {V U : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype U] [DecidableEq U] [Nonempty U]
    (a b : ℕ) (s : Finset V) (z : Finset U)
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * s.card ≤ a) (hz : 2 * z.card ≤ b) :
    Real.exp ((-(s.card : ℝ) ^ 2 / a - (s.card : ℝ) ^ 2 / (2 * Fintype.card V)) +
        (-(z.card : ℝ) ^ 2 / b - (z.card : ℝ) ^ 2 / (2 * Fintype.card U))) *
      (((a : ℝ) / Fintype.card V) ^ s.card *
        (1 + (b : ℝ) / Fintype.card U) ^ z.card) ≤
      (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset V) a,
        ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset U) b,
          (∏ i ∈ s, (M i : ℝ)) * (∏ j ∈ z, ((N j : ℝ) + 1))) /
        ((Finset.finsuppAntidiag (Finset.univ : Finset V) a).card *
          (Finset.finsuppAntidiag (Finset.univ : Finset U) b).card : ℝ) := by
  rw [occupationAverage_tensor]
  have h₁ := occupationAverage_prod_lower a s ha hs
  have h₂ := occupationAverage_prod_add_one_lower b z hb hz
  have hprod := mul_le_mul h₁ h₂ (by positivity)
    (occupationAverage_nonneg a _ (fun M => by positivity))
  rw [Real.exp_add]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod

end Problem335

end

end OAI
