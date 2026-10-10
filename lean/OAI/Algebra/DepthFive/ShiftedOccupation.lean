import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace ShiftedOccupation

/-- The integer occupation after subtracting one path shift from another. -/
def signedSource {ι σ : Type*} [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ) (x : ι × σ) : ℤ :=
  (M x : ℤ) + sign x.1 * ((if x.2 = p x.1 then 1 else 0) -
    (if x.2 = q x.1 then 1 else 0))

/-- Conversion to natural occupations; exact whenever all signed entries are nonnegative. -/
def source {ι σ : Type*} [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ) : ι × σ → ℕ :=
  fun x => (signedSource M sign p q x).toNat

lemma source_cast {ι σ : Type*} [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M sign p q x) (x : ι × σ) :
    (source M sign p q x : ℤ) = signedSource M sign p q x :=
  Int.toNat_of_nonneg (h x)

lemma source_unique {ι σ : Type*} [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ)
    (N : ι × σ → ℕ)
    (hN : ∀ x, (N x : ℤ) = signedSource M sign p q x) :
    N = source M sign p q := by
  funext x
  rw [source, ← hN x]
  simp

/-- Validity of the integer shift is exactly the existence of a natural source occupation. -/
lemma exists_source_iff {ι σ : Type*} [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ) :
    (∃ N : ι × σ → ℕ, ∀ x, (N x : ℤ) = signedSource M sign p q x) ↔
      ∀ x, 0 ≤ signedSource M sign p q x := by
  constructor
  · rintro ⟨N, hN⟩ x
    rw [← hN x]
    positivity
  · intro h
    exact ⟨source M sign p q, source_cast M sign p q h⟩

/-- The two path contributions cancel in each layer, even before imposing validity. -/
lemma signedSource_layer_sum {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ) (t : ι) :
    (∑ a : σ, signedSource M sign p q (t, a)) = ∑ a : σ, (M (t, a) : ℤ) := by
  simp [signedSource, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

/-- Every layer total of a valid shifted natural occupation is unchanged. -/
lemma source_layer_sum {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M sign p q x) (t : ι) :
    (∑ a : σ, source M sign p q (t, a)) = ∑ a : σ, M (t, a) := by
  have he : (∑ a : σ, (source M sign p q (t, a) : ℤ)) =
      ∑ a : σ, (M (t, a) : ℤ) := by
    simp_rw [source_cast M sign p q h]
    exact signedSource_layer_sum M sign p q t
  exact_mod_cast he

/-- In particular, both bidegrees are preserved for any partition into whole layers. -/
lemma source_layers_sum {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (M : ι × σ → ℕ) (sign : ι → ℤ) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M sign p q x) (layers : Finset ι) :
    (∑ t ∈ layers, ∑ a : σ, source M sign p q (t, a)) =
      ∑ t ∈ layers, ∑ a : σ, M (t, a) := by
  apply Finset.sum_congr rfl
  intro t ht
  exact source_layer_sum M sign p q h t

end ShiftedOccupation
end Problem335

end

end OAI
