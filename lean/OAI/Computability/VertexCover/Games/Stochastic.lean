import Mathlib
import OAI.Computability.VertexCover.Games.Value

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                     
section

namespace UniqueGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

theorem table_eval_pushforward [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (q₀ : Q) :
    (table responses).pushforward (fun answers => answers q₀) = responses q₀ := by
  classical
  apply eq_of_weight_eq
  intro a
  calc
    _ = (table responses).expectation
        (fun answers => if answers q₀ = a then 1 else 0) := by
      simp [pushforward, expectation, mul_ite]
    _ = (responses q₀).expectation (fun b => if b = a then 1 else 0) :=
      expectation_table_eval responses q₀ (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [expectation, mul_ite]

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]
end FiniteDistribution

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def responseTableLaw (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    FiniteDistribution (Strategy Q₁ Q₂ A₁ A₂) := by
  classical
  exact (FiniteDistribution.table responses₁).product (FiniteDistribution.table responses₂)

def stochasticSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) : ℝ :=
  G.questions.expectation (fun q =>
    (responses₁ q.1).expectation (fun a =>
      (responses₂ q.2).expectation (fun b =>
        if G.accepts q.1 q.2 a b then 1 else 0)))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem success_eq_question_expectation (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    G.success strategy = G.questions.expectation
      (fun q => if G.wins strategy q then 1 else 0) := by
  simp [success, FiniteDistribution.probability,
    FiniteDistribution.expectation, mul_ite]

theorem table_success_eq_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    (responseTableLaw responses₁ responses₂).expectation G.success =
      G.stochasticSuccess responses₁ responses₂ := by
  classical
  unfold stochasticSuccess
  calc
    _ = (responseTableLaw responses₁ responses₂).expectation
        (fun strategy => G.questions.expectation
          (fun q => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_congr _ (G.success_eq_question_expectation)
    _ = G.questions.expectation (fun q =>
        (responseTableLaw responses₁ responses₂).expectation
          (fun strategy => if G.wins strategy q then 1 else 0)) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro q
      rw [responseTableLaw, FiniteDistribution.expectation_product]
      change (FiniteDistribution.table responses₁).expectation
        (fun answers₁ => (FiniteDistribution.table responses₂).expectation
          (fun answers₂ =>
            if G.accepts q.1 q.2 (answers₁ q.1) (answers₂ q.2) then 1 else 0)) = _
      calc
        _ = (FiniteDistribution.table responses₁).expectation
            (fun answers₁ => (responses₂ q.2).expectation
              (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then 1 else 0)) := by
          apply FiniteDistribution.expectation_congr
          intro answers₁
          exact FiniteDistribution.expectation_table_eval responses₂ q.2
            (fun b => if G.accepts q.1 q.2 (answers₁ q.1) b then (1 : ℝ) else 0)
        _ = _ := FiniteDistribution.expectation_table_eval responses₁ q.1
          (fun a => (responses₂ q.2).expectation
            (fun b => if G.accepts q.1 q.2 a b then (1 : ℝ) else 0))

variable [Nonempty A₁] [Nonempty A₂]

theorem stochasticSuccess_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    G.stochasticSuccess responses₁ responses₂ ≤ G.value := by
  classical
  rw [← G.table_success_eq_stochastic]
  exact G.randomized_success_le_value (responseTableLaw responses₁ responses₂) id

theorem exists_deterministic_ge_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂,
      G.stochasticSuccess responses₁ responses₂ ≤ G.success strategy := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  refine ⟨strategy, ?_⟩
  rw [h]
  exact G.stochasticSuccess_le_value responses₁ responses₂
end Game
end
end UniqueGames.Foundations.Games

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
