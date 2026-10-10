import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.UniqueGames.Foundations.KernelSampling

namespace OAI

section

namespace PerfectCompleteness.DecoderTableCoupling

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]

theorem probability_eq_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite,
    mul_one, mul_zero]

theorem table_eq_product (responses : Q → FiniteDistribution A) :
    FiniteDistribution.table responses = FiniteProduct.law responses :=
  FiniteDistribution.eq_of_weight_eq (fun _ => rfl)

theorem pair_law_of_ne (responses : Q → FiniteDistribution A)
    (q r : Q) (hne : q ≠ r) :
    (FiniteDistribution.table responses).pushforward (fun f => (f q, f r)) =
      (responses q).product (responses r) := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨a, b⟩
  calc
    _ = (FiniteDistribution.table responses).expectation
        (fun f => (if f q = a then 1 else 0) * (if f r = b then 1 else 0)) := by
      unfold FiniteDistribution.pushforward FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro f _
      by_cases hq : f q = a <;> by_cases hr : f r = b <;> simp [hq, hr]
    _ = (responses q).expectation (fun a' => if a' = a then 1 else 0) *
        (responses r).expectation (fun b' => if b' = b then 1 else 0) := by
      rw [table_eq_product]
      exact FiniteProduct.expectation_eval_mul responses q r hne
        (fun a' : A => if a' = a then (1 : ℝ) else 0)
        (fun b' : A => if b' = b then (1 : ℝ) else 0)
    _ = _ := by simp [FiniteDistribution.expectation, FiniteDistribution.product, mul_ite]

def definedEqual (a b : Option A) : Bool :=
  decide (∃ value, a = some value ∧ b = some value)

omit [Fintype A] in
@[simp] theorem definedEqual_none_left (a : Option A) : definedEqual none a = false := by
  simp [definedEqual]

omit [Fintype A] in
@[simp] theorem definedEqual_none_right (a : Option A) : definedEqual a none = false := by
  simp [definedEqual]

omit [Fintype A] in
@[simp] theorem definedEqual_self (a : Option A) : definedEqual a a = a.isSome := by
  cases a <;> simp [definedEqual]

omit [Fintype Q] [DecidableEq Q] [Fintype A] in
@[simp] theorem definedEqual_collision (f : Q → Option A) (q r : Q) :
    definedEqual (f q) (f r) = TwoResponseCollision.collision f (q, r) := rfl

def freshCollision (responses : Q → FiniteDistribution (Option A)) (q r : Q) : ℝ :=
  ((responses q).product (responses r)).probability (fun a => definedEqual a.1 a.2)

def frozenCollision (responses : Q → FiniteDistribution (Option A)) (q r : Q) : ℝ :=
  (FiniteDistribution.table responses).probability (fun f => definedEqual (f q) (f r))

theorem frozenCollision_of_ne (responses : Q → FiniteDistribution (Option A))
    (q r : Q) (hne : q ≠ r) :
    frozenCollision responses q r = freshCollision responses q r := by
  unfold frozenCollision freshCollision
  rw [← pair_law_of_ne responses q r hne, FiniteDistribution.probability_pushforward]

theorem frozenCollision_self (responses : Q → FiniteDistribution (Option A)) (q : Q) :
    frozenCollision responses q q = (responses q).probability Option.isSome := by
  unfold frozenCollision
  simp only [definedEqual_self]
  rw [← FiniteDistribution.table_eval_pushforward responses q,
    FiniteDistribution.probability_pushforward]

theorem product_probability_first {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (event : X → Bool) :
    (μ.product ν).probability (fun p => event p.1) = μ.probability event := by
  unfold FiniteDistribution.probability
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;>
    simp [FiniteDistribution.product, he, ← Finset.mul_sum, ν.normalized]

omit [Fintype Q] [DecidableEq Q] in
theorem freshCollision_self_le (responses : Q → FiniteDistribution (Option A)) (q : Q) :
    freshCollision responses q q ≤ (responses q).probability Option.isSome := by
  unfold freshCollision
  calc
    _ ≤ ((responses q).product (responses q)).probability (fun a => a.1.isSome) := by
      apply FiniteDistribution.probability_mono
      intro a ha
      obtain ⟨value, hleft, _⟩ := of_decide_eq_true ha
      simp only [hleft, Option.isSome_some]
    _ = _ := product_probability_first _ _ _

theorem freshCollision_le_frozenCollision
    (responses : Q → FiniteDistribution (Option A)) (q r : Q) :
    freshCollision responses q r ≤ frozenCollision responses q r := by
  by_cases hqr : q = r
  · subst r
    rw [frozenCollision_self]
    exact freshCollision_self_le responses q
  · exact (frozenCollision_of_ne responses q r hqr).symm.le

theorem mean_freshCollision_le_frozen
    (responses : Q → FiniteDistribution (Option A)) (questions : FiniteDistribution (Q × Q)) :
    questions.expectation (fun p => freshCollision responses p.1 p.2) ≤
      (FiniteDistribution.table responses).expectation
        (fun f => questions.probability (TwoResponseCollision.collision f)) := by
  calc
    _ ≤ questions.expectation (fun p => frozenCollision responses p.1 p.2) := by
      unfold FiniteDistribution.expectation
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (freshCollision_le_frozenCollision responses p.1 p.2)
        (questions.nonnegative p)
    _ = _ := by
      simp only [frozenCollision, probability_eq_expectation]
      exact FiniteDistribution.expectation_comm questions (FiniteDistribution.table responses)
        (fun p f => if definedEqual (f p.1) (f p.2) then (1 : ℝ) else 0)

theorem freshCollision_le_of_supported_tables
    (responses : Q → FiniteDistribution (Option A)) (questions : FiniteDistribution (Q × Q))
    (bound : ℝ)
    (hbound : ∀ f, (FiniteDistribution.table responses).weight f ≠ 0 →
      questions.probability (TwoResponseCollision.collision f) ≤ bound) :
    questions.expectation (fun p => freshCollision responses p.1 p.2) ≤ bound := by
  apply (mean_freshCollision_le_frozen responses questions).trans
  calc
    _ ≤ ∑ f, (FiniteDistribution.table responses).weight f * bound := by
      unfold FiniteDistribution.expectation
      apply Finset.sum_le_sum
      intro f _
      by_cases hf : (FiniteDistribution.table responses).weight f = 0
      · simp only [hf, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hbound f hf)
          ((FiniteDistribution.table responses).nonnegative f)
    _ = bound := by
      rw [← Finset.sum_mul, (FiniteDistribution.table responses).normalized, one_mul]

end
end PerfectCompleteness.DecoderTableCoupling

end

end OAI
