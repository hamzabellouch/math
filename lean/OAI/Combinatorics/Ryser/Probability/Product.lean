import OAI.Combinatorics.Ryser.Probability.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.FiniteLaw

section ProductCoordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]

theorem expectation_pi_product (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (μ i).expectation (f i) := by
  classical
  simp only [expectation, pi_weight]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (μ i).weight a * f i a)).symm

theorem expectation_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (f : A i → ℝ) :
    (pi μ).expectation (fun ω => f (ω i)) = (μ i).expectation f := by
  classical
  let g : ∀ j, A j → ℝ := fun j a => if h : j = i then f (h ▸ a) else 1
  have hg (ω : ∀ j, A j) : (∏ j, g j (ω j)) = f (ω i) := by
    dsimp only [g]
    simp only [Fintype.prod_dite_eq']
  have he (j : I) : (μ j).expectation (g j) =
      if h : j = i then (μ i).expectation f else 1 := by
    by_cases h : j = i
    · subst j
      simp [g]
    · simp [g, h, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ j, g j (ω j)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ j, (μ j).expectation (g j) := expectation_pi_product μ g
    _ = _ := by simp_rw [he]; simp

theorem prob_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (P : A i → Prop) :
    (pi μ).prob (fun ω => P (ω i)) = (μ i).prob P := by
  classical
  rw [prob_eq_expectation, prob_eq_expectation]
  exact expectation_pi_coordinate μ i (fun a => if P a then 1 else 0)

theorem prob_pi (μ : ∀ i, FiniteLaw (A i)) (P : ∀ i, A i → Prop) :
    (pi μ).prob (fun ω => ∀ i, P i (ω i)) = ∏ i, (μ i).prob (P i) := by
  classical
  rw [prob_eq_expectation]
  calc
    _ = (pi μ).expectation (fun ω => ∏ i, if P i (ω i) then 1 else 0) := by
      congr 1
      funext ω
      symm
      by_cases h : ∀ i, P i (ω i)
      · simpa only [ite_eq_left h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
      · simpa only [ite_eq_right h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
    _ = ∏ i, (μ i).expectation (fun a => if P i a then 1 else 0) :=
      expectation_pi_product μ (fun i a => if P i a then 1 else 0)
    _ = _ := by simp_rw [prob_eq_expectation]

end ProductCoordinates

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem prob_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (P : Ω → Prop) (Q : Γ → Prop) :
    (μ.prod ν).prob (fun z => P z.1 ∧ Q z.2) = μ.prob P * ν.prob Q := by
  classical
  simp only [prob, prod, Fintype.sum_prod_type]
  calc
    _ = ∑ ω, ∑ γ,
        (if P ω then μ.weight ω else 0) * (if Q γ then ν.weight γ else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.sum_congr rfl
      intro γ _
      by_cases hp : P ω <;> by_cases hq : Q γ <;> simp [hp, hq]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

def map (μ : FiniteLaw Ω) (f : Ω → Γ) : FiniteLaw Γ where
  weight γ := ∑ ω, if f ω = γ then μ.weight ω else 0
  nonneg γ := Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl
  total := by
    rw [Finset.sum_comm]
    simpa using μ.total

@[simp] theorem map_weight (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = ∑ ω, if f ω = γ then μ.weight ω else 0 := rfl

theorem map_weight_eq_prob (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = μ.prob (fun ω => f ω = γ) := rfl

theorem expectation_map (μ : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → ℝ) :
    (map μ f).expectation g = μ.expectation (fun ω => g (f ω)) := by
  unfold expectation
  simp only [map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

theorem prob_map (μ : FiniteLaw Ω) (f : Ω → Γ) (P : Γ → Prop) :
    (map μ f).prob P = μ.prob (fun ω => P (f ω)) := by
  rw [prob_eq_expectation, expectation_map, prob_eq_expectation]

theorem map_uniform_of_fiber_card_eq [Nonempty Ω] [Nonempty Γ] (f : Ω → Γ)
    (hfiber : ∀ y z : Γ,
      Nat.card {x : Ω // f x = y} = Nat.card {x : Ω // f x = z}) :
    (uniform Ω).map f = uniform Γ := by
  classical
  apply eq_uniform_of_weight_eq
  intro y z
  rw [map_weight_eq_prob, map_weight_eq_prob, uniform_prob, uniform_prob]
  have hc : (Finset.univ.filter (fun x : Ω => f x = y)).card =
      (Finset.univ.filter (fun x : Ω => f x = z)).card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hfiber y z
  rw [hc]

theorem map_uniform_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) :
    (uniform Ω).map e = uniform Γ := by
  classical
  apply ext_weight
  funext y
  simp [map, uniform, ← e.eq_symm_apply, Fintype.card_congr e]

theorem uniform_prod (Ω Γ : Type*) [Fintype Ω] [Fintype Γ]
    [Nonempty Ω] [Nonempty Γ] :
    uniform (Ω × Γ) = (uniform Ω).prod (uniform Γ) :=
  (eq_uniform_of_weight_eq ((uniform Ω).prod (uniform Γ)) (fun _ _ => rfl)).symm

theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    pi (fun i => uniform (A i)) = uniform (∀ i, A i) :=
  eq_uniform_of_weight_eq (pi (fun i => uniform (A i))) (fun _ _ => rfl)

theorem prob_prod_average (mu : FiniteLaw Ω) (nu : FiniteLaw Γ)
    (P : Ω × Γ → Prop) :
    (mu.prod nu).prob P = mu.expectation (fun x => nu.prob (fun y => P (x, y))) := by
  simp only [prob_eq_expectation]
  exact expectation_prod mu nu (fun z => if P z then 1 else 0)

theorem prob_prod_le_bad_add (mu : FiniteLaw Ω) (nu : FiniteLaw Γ)
    (P : Ω × Γ → Prop) (Bad : Ω → Prop) (b : ℝ) (hb : 0 ≤ b)
    (hgood : ∀ x, ¬Bad x → nu.prob (fun y => P (x, y)) ≤ b) :
    (mu.prod nu).prob P ≤ mu.prob Bad + b := by
  classical
  rw [prob_prod_average]
  calc
    _ ≤ mu.expectation (fun x => (if Bad x then (1 : ℝ) else 0) + b) := by
      apply expectation_mono
      intro x
      by_cases hx : Bad x
      · simp only [ite_eq_left hx]
        exact (nu.prob_le_one _).trans (le_add_of_nonneg_right hb)
      · simpa only [ite_eq_right hx, zero_add] using hgood x hx
    _ = mu.prob Bad + b := by
      rw [expectation_add, expectation_const, ← prob_eq_expectation]

theorem prob_uniform_prod_equiv {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    (e : X ≃ Y × Z) (P : X → Prop) :
    (uniform X).prob P = (uniform Y).expectation
      (fun x => (uniform Z).prob (fun y => P (e.symm (x, y)))) := by
  calc
    _ = ((uniform X).map e).prob (fun z => P (e.symm z)) := by
      rw [prob_map]
      simp only [Equiv.symm_apply_apply]
    _ = _ := by rw [map_uniform_equiv, uniform_prod, prob_prod_average]

section UniformSplit

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty Ω]

theorem map_pi_uniform_split (p : I → Prop) [DecidablePred p] :
    (pi (fun _ : I => uniform Ω)).map
      (Equiv.piEquivPiSubtypeProd p (fun _ => Ω)) =
    (uniform ({i : I // p i} → Ω)).prod (uniform ({i : I // ¬p i} → Ω)) := by
  rw [pi_uniform, map_uniform_equiv, uniform_prod]

theorem prob_pi_uniform_split (p : I → Prop) [DecidablePred p]
    (P : (I → Ω) → Prop) :
    (pi (fun _ : I => uniform Ω)).prob P =
    (uniform ({i : I // p i} → Ω)).expectation (fun x =>
      (uniform ({i : I // ¬p i} → Ω)).prob (fun y =>
        P ((Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm (x, y)))) := by
  rw [pi_uniform]
  exact prob_uniform_prod_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Ω)) P

theorem prob_pi_uniform_split_le (p : I → Prop) [DecidablePred p]
    (P : (I → Ω) → Prop) (b : ℝ)
    (h : ∀ x : {i : I // p i} → Ω,
      (uniform ({i : I // ¬p i} → Ω)).prob (fun y =>
        P ((Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm (x, y))) ≤ b) :
    (pi (fun _ : I => uniform Ω)).prob P ≤ b := by
  rw [prob_pi_uniform_split p P]
  calc
    _ ≤ (uniform ({i : I // p i} → Ω)).expectation (fun _ => b) :=
      expectation_mono _ h
    _ = b := expectation_const _ b

theorem prob_pi_uniform_split_le_bad (p : I → Prop) [DecidablePred p]
    (P : (I → Ω) → Prop) (Bad : ({i : I // p i} → Ω) → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (hgood : ∀ x : {i : I // p i} → Ω, ¬Bad x →
      (uniform ({i : I // ¬p i} → Ω)).prob (fun y =>
        P ((Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm (x, y))) ≤ b) :
    (pi (fun _ : I => uniform Ω)).prob P ≤
      (uniform ({i : I // p i} → Ω)).prob Bad + b := by
  rw [prob_pi_uniform_split p P]
  simpa only [prob_prod_average] using
    prob_prod_le_bad_add (uniform ({i : I // p i} → Ω))
      (uniform ({i : I // ¬p i} → Ω))
      (fun z => P ((Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm z)) Bad b hb hgood

end UniformSplit

end RyserCoveringCounterexample.FiniteLaw

end

end OAI
