import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

/-! Counting core for the secretary random-prefix law: a uniformly random
permutation sends each fixed finite set uniformly onto sets of the same size.
No conditioning on the complete secretary seed is asserted here.

Source: `sections/secretary.tex`, equation `eq:secretary-prefix-mask`,
lines 54--66 of the pinned manuscript; SHA256
`3554fe0f7296782edf63cc7f1305c377e7a7b9d8f8948b9510ea4ad02a702d63`.
These are supporting counting lemmas, not the complete secretary endpoint.
The empty ambient type and empty/full fixed subsets are included. -/

namespace MatroidProphet.Secretary

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Equal-cardinality target sets have equally many permutation preimages. -/
theorem permutation_image_count_eq (s t u : Finset α) (htu : t.card = u.card) :
    (∑ σ : Equiv.Perm α, if s.map σ.toEmbedding = t then (1 : ℝ) else 0) =
      ∑ σ : Equiv.Perm α, if s.map σ.toEmbedding = u then (1 : ℝ) else 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_map_finset_eq t u htu
  let e : Equiv.Perm α ≃ Equiv.Perm α :=
    { toFun := fun σ => σ.trans ρ
      invFun := fun σ => σ.trans ρ.symm
      left_inv := fun σ => by ext a; simp
      right_inv := fun σ => by ext a; simp }
  have he (σ : Equiv.Perm α) :
      s.map (e σ).toEmbedding = u ↔ s.map σ.toEmbedding = t := by
    have hmap : s.map (e σ).toEmbedding = (s.map σ.toEmbedding).map ρ.toEmbedding := by
      simp [e, Finset.map_map, Function.Embedding.trans]
    rw [hmap, ← hρ]
    exact Finset.map_injective ρ.toEmbedding |>.eq_iff
  calc
    _ = ∑ σ : Equiv.Perm α, if s.map (e σ).toEmbedding = u then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      simp only [he]
    _ = _ := e.sum_comp (fun σ => if s.map σ.toEmbedding = u then (1 : ℝ) else 0)

/-- Exact probability numerator for a prescribed image of a fixed set. -/
theorem permutation_image_count (s t : Finset α) (hst : s.card = t.card) :
    (∑ σ : Equiv.Perm α, if s.map σ.toEmbedding = t then (1 : ℝ) else 0) =
      (Fintype.card (Equiv.Perm α) : ℝ) / (Fintype.card α).choose s.card := by
  classical
  let C : ℝ := ∑ σ : Equiv.Perm α, if s.map σ.toEmbedding = t then (1 : ℝ) else 0
  let T := (Finset.univ : Finset α).powersetCard s.card
  have hT (u : Finset α) : u ∈ T ↔ u.card = s.card := by
    simp [T]
  have hsum : (Nat.choose (Fintype.card α) s.card : ℝ) * C =
      Fintype.card (Equiv.Perm α) := by
    calc
      _ = ∑ u ∈ T, C := by simp [T, Finset.card_powersetCard]
      _ = ∑ u ∈ T, ∑ σ : Equiv.Perm α,
          if s.map σ.toEmbedding = u then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact permutation_image_count_eq s t u (hst.symm.trans (hT u |>.mp hu).symm)
      _ = ∑ σ : Equiv.Perm α, ∑ u ∈ T,
          if s.map σ.toEmbedding = u then (1 : ℝ) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ _ : Equiv.Perm α, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro σ _
        have hmem : s.map σ.toEmbedding ∈ T := (hT _).2 (Finset.card_map _)
        simp [hmem]
      _ = _ := by simp
  have hc : (Nat.choose (Fintype.card α) s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Finset.card_le_univ s)).ne'
  apply (eq_div_iff hc).2
  simpa only [mul_comm] using hsum

/-- A prescribed image has probability the reciprocal of the number of
sets of that size, and probability zero if its cardinality is different. -/
theorem uniform_permutation_image_atom (s t : Finset α) :
    (∑ σ : Equiv.Perm α, if s.map σ.toEmbedding = t then (1 : ℝ) else 0) /
        Fintype.card (Equiv.Perm α) =
      if s.card = t.card then ((Fintype.card α).choose s.card : ℝ)⁻¹ else 0 := by
  classical
  by_cases hst : s.card = t.card
  · rw [ite_eq_left hst, permutation_image_count s t hst]
    have hc : (Fintype.card (Equiv.Perm α) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm α) ≠ 0)
    field_simp
  · rw [ite_eq_right hst]
    have hne (σ : Equiv.Perm α) : s.map σ.toEmbedding ≠ t := by
      intro h
      apply hst
      simpa using congrArg Finset.card h
    simp [hne]

/-- Averaging over all permutations equals averaging over all possible
images of the fixed set. This form can be mixed over a random prefix length. -/
theorem uniform_permutation_image_average (s : Finset α) (f : Finset α → ℝ) :
    (∑ σ : Equiv.Perm α, f (s.map σ.toEmbedding)) /
        Fintype.card (Equiv.Perm α) =
      (∑ t ∈ (Finset.univ : Finset α).powersetCard s.card, f t) /
        (Fintype.card α).choose s.card := by
  classical
  let T := (Finset.univ : Finset α).powersetCard s.card
  have hT (t : Finset α) : t ∈ T ↔ t.card = s.card := by simp [T]
  calc
    _ = (∑ σ : Equiv.Perm α, ∑ t ∈ T,
        (if s.map σ.toEmbedding = t then (1 : ℝ) else 0) * f t) /
          Fintype.card (Equiv.Perm α) := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      have hmem : s.map σ.toEmbedding ∈ T := (hT _).2 (Finset.card_map _)
      simp [hmem]
    _ = ∑ t ∈ T, ((∑ σ : Equiv.Perm α,
        if s.map σ.toEmbedding = t then (1 : ℝ) else 0) /
          Fintype.card (Equiv.Perm α)) * f t := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_mul]
      ring
    _ = ∑ t ∈ T, (((Fintype.card α).choose s.card : ℝ)⁻¹ * f t) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [uniform_permutation_image_atom, ite_eq_left ((hT t).1 ht).symm]
    _ = _ := by
      rw [← Finset.mul_sum]
      change _ = (∑ t ∈ T, f t) / _
      rw [div_eq_mul_inv, mul_comm]

end MatroidProphet.Secretary

end OAI
