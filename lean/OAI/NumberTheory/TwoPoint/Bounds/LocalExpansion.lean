import OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
import OAI.NumberTheory.TwoPoint.PretentiousDistance
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Finite local expansions

The local sequences in manuscript Lemma `lem:affine-dilation` have value zero
at exponent zero. A difference of two normalized local sequences represents
such a sequence. Expansion over subsets then produces ordinary multiplicative
components that retain the original prime values outside the fixed finite set.
-/

open scoped BigOperators

namespace TwoPointCorrelations

/-- A normalized multiplicative component with one of two local choices at each
prime in `P`. -/
noncomputable def localComponent (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) : ℕ → ℂ :=
  fromPrimePowers (fun p k => if p ∈ P then if p ∈ E then C p k else B p k else f (p ^ k))

theorem localComponent_multiplicative (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) : Multiplicative (localComponent f B C P E) :=
  fromPrimePowers_multiplicative _

theorem localComponent_oneBounded (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) (hf : OneBounded f)
    (hB : ∀ p k, p ∈ P → 0 < k → ‖B p k‖ ≤ 1)
    (hC : ∀ p k, p ∈ P → 0 < k → ‖C p k‖ ≤ 1) :
    OneBounded (localComponent f B C P E) := by
  apply fromPrimePowers_oneBounded
  intro p k hp hk
  split_ifs with hpP hpE
  · exact hC p k hpP hk
  · exact hB p k hpP hk
  · exact hf _ (pow_pos hp.pos _)

theorem localComponent_prime (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) :
    localComponent f B C P E p = f p := by
  simp [localComponent, fromPrimePowers_prime _ hp, hpP]

/-- Expanding the support of a prime-power product is valid when the additional
local factors have value one at exponent zero. -/
theorem fromPrimePowers_split (F : ℕ → ℕ → ℂ) (P : Finset ℕ)
    (hF : ∀ p, F p 0 = 1) (n : ℕ) :
    fromPrimePowers F n =
      (∏ p ∈ P, F p (n.factorization p)) *
        ∏ p ∈ n.primeFactors \ P, F p (n.factorization p) := by
  unfold fromPrimePowers
  rw [Finsupp.prod_of_support_subset _ (s := P ∪ n.primeFactors)
    (by simp) F (fun p _ => hF p)]
  rw [← Finset.union_sdiff_self_eq_union (s := P) (t := n.primeFactors),
    Finset.prod_union disjoint_sdiff_self_left.symm]

theorem localComponent_split (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) (hE : E ⊆ P) (hf : f 1 = 1)
    (hB : ∀ p, B p 0 = 1) (hC : ∀ p, C p 0 = 1) (n : ℕ) :
    localComponent f B C P E n =
      ((∏ p ∈ P \ E, B p (n.factorization p)) * ∏ p ∈ E, C p (n.factorization p)) *
        ∏ p ∈ n.primeFactors \ P, f (p ^ n.factorization p) := by
  unfold localComponent
  rw [fromPrimePowers_split _ P (by intro p; simp [hB, hC, hf])]
  congr 1
  · rw [← Finset.sdiff_union_of_subset hE, Finset.prod_union Finset.sdiff_disjoint]
    congr 1
    · simp only [Finset.union_sdiff_cancel_right (Finset.sdiff_disjoint)]
      apply Finset.prod_congr rfl
      intro p hp
      have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
      have hpE : p ∉ E := (Finset.mem_sdiff.mp hp).2
      simp [hpP, hpE]
    · apply Finset.prod_congr rfl
      intro p hp
      simp [hp, hE hp]
  · apply Finset.prod_congr rfl
    intro p hp
    simp [(Finset.mem_sdiff.mp hp).2]

/-- Exact finite expansion with one normalized multiplicative component for
each subset of the exceptional primes. -/
theorem local_difference_expansion (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P : Finset ℕ) (hf : f 1 = 1)
    (hB : ∀ p, B p 0 = 1) (hC : ∀ p, C p 0 = 1) (n : ℕ) :
    (∏ p ∈ P, (B p (n.factorization p) - C p (n.factorization p))) *
        (∏ p ∈ n.primeFactors \ P, f (p ^ n.factorization p)) =
      ∑ E ∈ P.powerset, (-1 : ℂ) ^ E.card * localComponent f B C P E n := by
  rw [Finset.prod_sub, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  rw [localComponent_split f B C P E (Finset.mem_powerset.mp hE) hf hB hC n]
  ring

/-- Every bounded component inherits nonpretentiousness from the original
factor. This uses only changes at the fixed finite prime set. -/
theorem localComponent_nonpretentious (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (hB : ∀ p k, p ∈ P → 0 < k → ‖B p k‖ ≤ 1)
    (hC : ∀ p k, p ∈ P → 0 < k → ‖C p k‖ ≤ 1) :
    UniformlyNonpretentious (localComponent f B C P E) := by
  apply hfnp.finite_prime_change P hf (localComponent_oneBounded f B C P E hf hB hC)
  intro p hp hpP
  exact localComponent_prime f B C P E hp hpP

end TwoPointCorrelations

end OAI
