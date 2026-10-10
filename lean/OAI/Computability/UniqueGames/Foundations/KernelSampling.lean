import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI

section

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators
noncomputable section

namespace FiniteDistribution

theorem pushforward_eq_of_agree_on_support
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f g : Ω → Γ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.pushforward f = μ.pushforward g := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

/-- Applying separate maps to independent samples preserves their independence. -/
theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

/-- A full response table of nonzero weight uses a supported answer in every row. -/
theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

/-- Repairing table entries only off each row's support leaves its exact law intact. -/
theorem table_repair_pushforward
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (repair : Q → A → A)
    (hrepair : ∀ q a, (responses q).weight a ≠ 0 → repair q a = a) (q : Q) :
    (table responses).pushforward (fun answers => repair q (answers q)) =
      responses q := by
  calc
    _ = (table responses).pushforward (fun answers => answers q) := by
      apply pushforward_eq_of_agree_on_support
      intro answers h
      exact hrepair q (answers q) (table_row_weight_ne_zero responses answers h q)
    _ = responses q := table_eval_pushforward responses q

end FiniteDistribution

namespace KernelSampling

/-- A single seed supplies a full local table to each side. -/
abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

/-- The fixed weighted seed law; it does not depend on the sampled questions. -/
def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

/-- The two reads have exactly the product of the requested conditional laws. -/
theorem read_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed => (readLeft seed x, readRight seed y)) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => answers x) (fun answers => answers y),
    FiniteDistribution.table_eval_pushforward, FiniteDistribution.table_eval_pushforward]

/-- Separate supported repairs retain the exact joint product law. -/
theorem repaired_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (repairLeft : Q₁ → A → A) (repairRight : Q₂ → B → B)
    (hleft : ∀ x a, (left x).weight a ≠ 0 → repairLeft x a = a)
    (hright : ∀ y b, (right y).weight b ≠ 0 → repairRight y b = b)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed =>
      (repairLeft x (readLeft seed x), repairRight y (readRight seed y))) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => repairLeft x (answers x)) (fun answers => repairRight y (answers y)),
    FiniteDistribution.table_repair_pushforward left repairLeft hleft,
    FiniteDistribution.table_repair_pushforward right repairRight hright]

section Completion

variable {I A B S : Type*} [DecidableEq I]

/-- Restore the designated coordinate on every left table read. -/
def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

/-- Restore the designated coordinate on every right table read. -/
def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

private theorem update_eq_of_coordinate (xs : I → A) (j : I) (a : A)
    (h : xs j = a) : Function.update xs j a = xs := by
  funext i
  by_cases hi : i = j <;> simp [Function.update, hi, h]

/-- Exact conditional completion from a finite weighted shared seed. The reads
always restore the specified coordinates, including on seeds of weight zero;
the support hypotheses ensure that this repair preserves the requested laws. -/
theorem completed_joint_pushforward
    [Fintype I] [Fintype A] [Fintype B] [Fintype S]
    [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (left : (A × S) → FiniteDistribution (I → A))
    (right : (B × S) → FiniteDistribution (I → B)) (j : I)
    (hleft : ∀ q xs, (left q).weight xs ≠ 0 → xs j = q.1)
    (hright : ∀ q ys, (right q).weight ys ≠ 0 → ys j = q.1)
    (x : A × S) (y : B × S) :
    (seedLaw left right).pushforward
        (fun seed => (completedLeft j seed x, completedRight j seed y)) =
      (left x).product (right y) := by
  apply repaired_joint_pushforward left right
    (fun q xs => Function.update xs j q.1) (fun q ys => Function.update ys j q.1)
  · intro q xs h
    exact update_eq_of_coordinate xs j q.1 (hleft q xs h)
  · intro q ys h
    exact update_eq_of_coordinate ys j q.1 (hright q ys h)

end Completion

end KernelSampling
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
