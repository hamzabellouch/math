import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordProgram
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.FiniteRepetition

namespace OAI

/-! # Finite tuples drawn by sequential fair-word reads -/

noncomputable section
namespace LowSpaceSubsetSum.WordTuple

open scoped BigOperators
open WordProgram

variable {w : ℕ}

def sample : (N : ℕ) → Program w (Fin N → Fin (2^w))
  | 0 => .pure Fin.elim0
  | N+1 => .draw (fun x => WordProgram.map (Fin.cons x) (sample N))

theorem bounded (N : ℕ) : Bounded (sample (w := w) N) N := by
  induction N with
  | zero => exact Bounded.pure _ 0
  | succ N ih =>
    apply Bounded.draw
    intro x
    simpa only [WordProgram.map, Nat.add_zero] using
      WordProgram.bind_bound (sample N) N ih (fun f : Fin N → Fin (2^w) => .pure (Fin.cons (n := N) (α := fun _ => Fin (2^w)) x f)) 0
        (fun _ => Bounded.pure _ 0)

private theorem uniform_product {α β : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    (FiniteLaw.uniform : FiniteLaw (α × β)) =
      (FiniteLaw.uniform : FiniteLaw α).prod (FiniteLaw.uniform : FiniteLaw β) := by
  apply FiniteLaw.eq_of_mass
  intro p
  simp only [FiniteLaw.uniform, FiniteLaw.prod, Fintype.card_prod, Nat.cast_mul]
  exact (one_div_mul_one_div _ _).symm

private theorem product_expectation {α β : Type} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α × β → ℝ) :
    (μ.prod ν).expectation f = μ.expectation (fun a => ν.expectation (fun b => f (a,b))) := by
  simp only [FiniteLaw.expectation, FiniteLaw.prod, Fintype.sum_prod_type, Finset.mul_sum,
    mul_assoc]

private theorem uniform_word_expectation (f : Fin (2^w) → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin (2^w))).expectation f =
      (∑ x, f x) / (2^w : ℕ) := by
  simp only [FiniteLaw.expectation, FiniteLaw.uniform, Fintype.card_fin,
    one_div_mul_eq_div, Finset.sum_div]

theorem cons_expectation (N : ℕ) (f : (Fin (N+1) → Fin (2^w)) → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin (N+1) → Fin (2^w))).expectation f =
      (∑ x, (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).expectation
        (fun xs => f (Fin.cons x xs))) / (2^w : ℕ) := by
  have he := FiniteLaw.map_equiv_uniform (Fin.consEquiv (fun _ : Fin (N+1) => Fin (2^w)))
  rw [← he, FiniteLaw.map_expectation, uniform_product, product_expectation,
    uniform_word_expectation]
  rfl

theorem expectation (N : ℕ) (f : (Fin N → Fin (2^w)) → ℝ) :
    WordProgram.expectation (sample N) f =
      (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).expectation f := by
  induction N with
  | zero =>
    simp only [sample, WordProgram.expectation, FiniteLaw.expectation, FiniteLaw.uniform,
      Fintype.card_unique, Nat.cast_one, div_one, one_mul, Finset.univ_unique,
      Finset.sum_singleton]
    rfl
  | succ N ih =>
    rw [cons_expectation]
    simp only [sample, WordProgram.expectation, WordProgram.map, WordProgram.expectation_bind]
    simp only [ih]

theorem probability (N : ℕ) (P : (Fin N → Fin (2^w)) → Prop) :
    WordProgram.probability (sample N) P =
      (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).probability P := by
  classical
  rw [WordProgram.probability, expectation, ← FiniteLaw.probability_eq_expectation]

end LowSpaceSubsetSum.WordTuple

end

end OAI
