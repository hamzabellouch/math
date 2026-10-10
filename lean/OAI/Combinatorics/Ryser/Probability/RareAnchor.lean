import Mathlib.Tactic.Ring
import OAI.Combinatorics.Ryser.Probability.Finite

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample

lemma rareAnchor_centering_raw
    {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (htotal : (∑ ω, w ω) = 1)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : (∑ ω, if E ω then w ω else 0) ≤ r) :
    let m := ∑ ω, w ω * g ω
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r := by
  classical
  let m : ℝ := ∑ ω, w ω * g ω
  change
    (∑ ω, w ω * (g ω - m)) = 0 ∧
      (∀ ω, |g ω - m| ≤ 2 * C) ∧
      (∑ ω, w ω * (g ω - m) ^ 2) ≤ C ^ 2 * r

  have hconst (a : ℝ) : (∑ ω, w ω * a) = a := by
    rw [← Finset.sum_mul, htotal, one_mul]

  have hmlo : b - C ≤ m := by
    calc
      b - C = ∑ ω, w ω * (b - C) := (hconst _).symm
      _ ≤ ∑ ω, w ω * g ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hlo := (abs_le.mp (hbound ω)).1
        linarith
      _ = m := rfl

  have hmhi : m ≤ b + C := by
    calc
      m = ∑ ω, w ω * g ω := rfl
      _ ≤ ∑ ω, w ω * (b + C) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        have hhi := (abs_le.mp (hbound ω)).2
        linarith
      _ = b + C := hconst _

  have hmean0 : (∑ ω, w ω * (g ω - m)) = 0 := by
    calc
      (∑ ω, w ω * (g ω - m)) =
          (∑ ω, w ω * g ω) - (∑ ω, w ω * m) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ = m - m := by
        change m - (∑ ω, w ω * m) = m - m
        rw [hconst m]
      _ = 0 := sub_self m

  have hcenterBound : ∀ ω, |g ω - m| ≤ 2 * C := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor <;> linarith

  have hsqBound : ∀ ω, (g ω - b) ^ 2 ≤ C ^ 2 := by
    intro ω
    rcases abs_le.mp (hbound ω) with ⟨hlo, hhi⟩
    have hminus : 0 ≤ C - (g ω - b) := by
      linarith
    have hplus : 0 ≤ C + (g ω - b) := by
      linarith
    have hprod := mul_nonneg hminus hplus
    nlinarith

  have hanchor :
      (∑ ω, w ω * (g ω - b) ^ 2) ≤ C ^ 2 * r := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) ≤
          ∑ ω, (if E ω then w ω else 0) * C ^ 2 := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases hE : E ω
        · simp only [ite_eq_left hE]
          exact mul_le_mul_of_nonneg_left (hsqBound ω) (hw ω)
        · simp [hE, houtside ω hE]
      _ = (∑ ω, if E ω then w ω else 0) * C ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ r * C ^ 2 :=
        mul_le_mul_of_nonneg_right hrare (sq_nonneg C)
      _ = C ^ 2 * r := mul_comm _ _

  have hvariance :
      (∑ ω, w ω * (g ω - b) ^ 2) =
        (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
    calc
      (∑ ω, w ω * (g ω - b) ^ 2) =
          ∑ ω,
            (w ω * (g ω - m) ^ 2 +
              (w ω * (g ω - m)) * (2 * (m - b)) +
              w ω * (m - b) ^ 2) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = (∑ ω, w ω * (g ω - m) ^ 2) +
            (∑ ω, w ω * (g ω - m)) * (2 * (m - b)) +
            (∑ ω, w ω) * (m - b) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul]
      _ = (∑ ω, w ω * (g ω - m) ^ 2) + (m - b) ^ 2 := by
        simp only [hmean0, htotal, zero_mul, one_mul, add_zero]

  refine ⟨hmean0, hcenterBound, ?_⟩
  have hshiftNonneg := sq_nonneg (m - b)
  linarith [hvariance, hanchor]

lemma FiniteLaw.rareAnchor_centering
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (g : Ω → ℝ) (b C r : ℝ)
    (E : Ω → Prop) [DecidablePred E]
    (hbound : ∀ ω, |g ω - b| ≤ C)
    (houtside : ∀ ω, ¬ E ω → g ω = b)
    (hrare : μ.prob E ≤ r) :
    μ.expectation (fun ω => g ω - μ.expectation g) = 0 ∧
      (∀ ω, |g ω - μ.expectation g| ≤ 2 * C) ∧
      μ.expectation (fun ω => (g ω - μ.expectation g) ^ 2)
        ≤ C ^ 2 * r := by
  exact @rareAnchor_centering_raw Ω _
    μ.weight μ.nonneg μ.total g b C r E
    (fun ω => Classical.propDecidable (E ω))
    hbound houtside hrare

end RyserCoveringCounterexample

end OAI
