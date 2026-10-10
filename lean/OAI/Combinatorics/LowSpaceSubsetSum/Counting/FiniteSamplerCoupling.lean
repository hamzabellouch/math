import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteKernels
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.BoundedSampling

namespace OAI

/-! # Explicit finite couplings for dependent bounded samplers

The source retains fresh candidate tuples and independent backup choices.
The backup is used only by the ideal completion of an exhausted call; the
bounded output is `none` at that point. No law is conditioned on every call
succeeding.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace FiniteLaw

variable {Ω α : Type*} [Fintype Ω] [Fintype α]

def map (μ : FiniteLaw Ω) (f : Ω → α) : FiniteLaw α where
  mass a := μ.probability (fun x => f x = a)
  nonneg _ := μ.probability_nonneg _
  total := by
    classical
    simp only [probability]
    rw [Finset.sum_comm]
    simpa using μ.total

def expectation (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ x, μ.mass x * f x

theorem map_expectation (μ : FiniteLaw Ω) (f : Ω → α) (g : α → ℝ) :
    (μ.map f).expectation g = μ.expectation (fun x => g (f x)) := by
  classical
  simp only [expectation, map, probability, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem probability_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.probability P = μ.expectation (fun x => if P x then 1 else 0) := by
  classical
  simp only [probability, expectation, mul_ite, mul_one, mul_zero]

theorem map_probability (μ : FiniteLaw Ω) (f : Ω → α) (P : α → Prop) :
    (μ.map f).probability P = μ.probability (fun x => P (f x)) := by
  classical
  rw [probability_eq_expectation, map_expectation, probability_eq_expectation]

theorem probability_or_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.probability (fun x => P x ∨ Q x) ≤ μ.probability P + μ.probability Q := by
  classical
  simp only [probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq, μ.nonneg x]

end FiniteLaw

/-- An explicit common probability space for an ideal result and a bounded
result. Every nonfailure agrees exactly; failure remains part of the law. -/
structure SamplerCoupling (α : Type*) [Fintype α] where
  Seed : Type
  finiteSeed : Fintype Seed
  law : @FiniteLaw Seed finiteSeed
  ideal : Seed → α
  bounded : Seed → Option α
  agrees : ∀ s, bounded s = none ∨ bounded s = some (ideal s)

namespace SamplerCoupling

variable {α : Type*} [Fintype α]

instance (S : SamplerCoupling α) : Fintype S.Seed := S.finiteSeed

def idealLaw (S : SamplerCoupling α) : FiniteLaw α := S.law.map S.ideal

def boundedLaw (S : SamplerCoupling α) : FiniteLaw (Option α) := S.law.map S.bounded

def failure (S : SamplerCoupling α) : ℝ := S.law.probability (fun s => S.bounded s = none)

def pure (a : α) : SamplerCoupling α where
  Seed := Unit
  finiteSeed := inferInstance
  law := FiniteLaw.uniform
  ideal _ := a
  bounded _ := some a
  agrees _ := Or.inr rfl

def bind (S : SamplerCoupling α) (β : α → Type) [∀ a, Fintype (β a)]
    (T : ∀ a, SamplerCoupling (β a)) : SamplerCoupling (Σ a, β a) where
  Seed := Σ s : S.Seed, (T (S.ideal s)).Seed
  finiteSeed := inferInstance
  law := S.law.bind (fun s => (T (S.ideal s)).Seed) (fun s => (T (S.ideal s)).law)
  ideal s := ⟨S.ideal s.1, (T (S.ideal s.1)).ideal s.2⟩
  bounded s := if S.bounded s.1 = none then none else
    ((T (S.ideal s.1)).bounded s.2).map (fun b => ⟨S.ideal s.1, b⟩)
  agrees s := by
    classical
    split
    · exact Or.inl rfl
    · rcases (T (S.ideal s.1)).agrees s.2 with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])

/-- The ideal marginal follows the exact prescribed conditional laws. -/
theorem bind_ideal_probability (S : SamplerCoupling α) (β : α → Type)
    [∀ a, Fintype (β a)] (T : ∀ a, SamplerCoupling (β a))
    (P : (Σ a, β a) → Prop) :
    (S.bind β T).idealLaw.probability P =
      (S.idealLaw.bind β (fun a => (T a).idealLaw)).probability P := by
  classical
  rw [idealLaw, FiniteLaw.map_probability]
  change (S.law.bind (fun s => (T (S.ideal s)).Seed)
    (fun s => (T (S.ideal s)).law)).probability
      (fun z => P ⟨S.ideal z.1, (T (S.ideal z.1)).ideal z.2⟩) = _
  rw [FiniteLaw.bind_probability, FiniteLaw.bind_probability]
  change S.law.expectation (fun s =>
    (T (S.ideal s)).law.probability (fun t => P ⟨S.ideal s, (T (S.ideal s)).ideal t⟩)) = _
  have hpoint (a : α) : (T a).law.probability
      (fun t => P ⟨a, (T a).ideal t⟩) =
      (T a).idealLaw.probability (fun b => P ⟨a, b⟩) :=
    (FiniteLaw.map_probability (T a).law (T a).ideal (fun b => P ⟨a, b⟩)).symm
  simp_rw [hpoint]
  exact (FiniteLaw.map_expectation S.law S.ideal
    (fun a => (T a).idealLaw.probability (fun b => P ⟨a, b⟩))).symm

/-- The probability of first divergence is at most the previous loss plus
the uniform conditional bound for the next call. -/
theorem bind_failure_le (S : SamplerCoupling α) (β : α → Type)
    [∀ a, Fintype (β a)] (T : ∀ a, SamplerCoupling (β a))
    (δ : ℝ) (hT : ∀ a, (T a).failure ≤ δ) :
    (S.bind β T).failure ≤ S.failure + δ := by
  classical
  let L := S.law.bind (fun s => (T (S.ideal s)).Seed) (fun s => (T (S.ideal s)).law)
  have he : (S.bind β T).failure = L.probability (fun s =>
      S.bounded s.1 = none ∨ (T (S.ideal s.1)).bounded s.2 = none) := by
    apply congrArg L.probability
    funext s
    apply propext
    simp only [bind]
    split <;> simp_all
  rw [he]
  apply (L.probability_or_le _ _).trans
  have hfirst : L.probability (fun s => S.bounded s.1 = none) = S.failure :=
    FiniteLaw.bind_first_probability S.law (fun s => (T (S.ideal s)).Seed)
      (fun s => (T (S.ideal s)).law) (fun s => S.bounded s = none)
  rw [hfirst]
  apply add_le_add (le_refl _)
  dsimp only [L]
  rw [FiniteLaw.bind_probability]
  calc
    _ ≤ ∑ s, S.law.mass s * δ := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hT (S.ideal s)) (S.law.nonneg s)
    _ = δ := by rw [← Finset.sum_mul, S.law.total, one_mul]

/-- Every ideal event loses at most the unconditional coupling failure. -/
theorem event_lower (S : SamplerCoupling α) (P : α → Prop) :
    S.idealLaw.probability P - S.failure ≤
      S.boundedLaw.probability (fun x => ∃ a, x = some a ∧ P a) := by
  classical
  rw [idealLaw, boundedLaw, FiniteLaw.map_probability, FiniteLaw.map_probability, failure]
  have hi := S.law.probability_inter_ge_sub (fun s => P (S.ideal s))
    (fun s => S.bounded s ≠ none)
  simp only [not_not] at hi
  apply hi.trans
  apply S.law.probability_mono
  intro s hs
  rcases S.agrees s with hf | he
  · exact (hs.2 hf).elim
  · exact ⟨S.ideal s, he, hs.1⟩

end SamplerCoupling
end LowSpaceSubsetSum

end

end OAI
