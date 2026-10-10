import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

namespace OAI

/-!
# Finite sums over embedded prefixes

A function supported on the image of an embedding can be summed over its
domain. For an ordered retained-candidate embedding, its natural prefix
before a candidate agrees with the prefix of retained nodes before that node.
-/

namespace ReflexiveFixedPoints.FinitePrefix

open scoped BigOperators

variable {M : Type*} [AddCommMonoid M]

/-- Reindex a finite sum whose summands vanish outside an embedding's image. -/
theorem sum_univ_supported_embedding {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (f : B → M)
    (hf : ∀ b, (¬ ∃ a, e a = b) → f b = 0) :
    (∑ b, f b) = ∑ a, f (e a) := by
  classical
  calc
    (∑ b, f b) = ∑ b ∈ Finset.univ.map e, f b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _hb hnot
      apply hf b
      rintro ⟨a, rfl⟩
      exact hnot (Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩)
    _ = ∑ a, f (e a) := Finset.sum_map _ _ _

/-- The inclusion of an initial finite segment into a larger finite segment. -/
def inclusion {c q : ℕ} (h : q ≤ c) : Fin q ↪ Fin c :=
  Fin.castLEEmb h

@[simp]
theorem inclusion_apply {c q : ℕ} (h : q ≤ c) (i : Fin q) :
    inclusion h i = Fin.castLE h i := rfl

@[simp]
theorem inclusion_val {c q : ℕ} (h : q ≤ c) (i : Fin q) :
    (inclusion h i).val = i.val := rfl

/-- An initial-segment sum is a full sum with the complementary summands zeroed. -/
theorem sum_prefix_eq_sum_cutoff {c q : ℕ} (h : q ≤ c) (f : Fin c → M) :
    (∑ i : Fin q, f (inclusion h i)) =
      ∑ j : Fin c, if j.val < q then f j else 0 := by
  classical
  symm
  calc
    (∑ j : Fin c, if j.val < q then f j else 0) =
        ∑ i : Fin q, if (inclusion h i).val < q then f (inclusion h i) else 0 := by
      apply sum_univ_supported_embedding (inclusion h)
      intro b hb
      apply ite_eq_right
      intro hbq
      apply hb
      refine ⟨⟨b.val, hbq⟩, ?_⟩
      apply Fin.ext
      rfl
    _ = ∑ i : Fin q, f (inclusion h i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact ite_eq_left (show (inclusion h i).val < q from i.isLt)

/-- Summing supported candidate data before a retained candidate is exactly
summing the retained data before its retained node. -/
theorem sum_prefix_eq_sum_retained {n c : ℕ} (e : Fin n ↪o Fin c)
    (v : Fin n) (f : Fin c → M)
    (hf : ∀ b, (¬ ∃ a, e a = b) → f b = 0) :
    (∑ i : Fin (e v).val, f (inclusion (e v).isLt.le i)) =
      ∑ w : Fin n, if w < v then f (e w) else 0 := by
  classical
  calc
    (∑ i : Fin (e v).val, f (inclusion (e v).isLt.le i)) =
        ∑ j : Fin c, if j.val < (e v).val then f j else 0 :=
      sum_prefix_eq_sum_cutoff (e v).isLt.le f
    _ = ∑ w : Fin n, if (e w).val < (e v).val then f (e w) else 0 := by
      apply sum_univ_supported_embedding e.toEmbedding
      intro b hb
      simp only [hf b hb, ite_self]
    _ = ∑ w : Fin n, if w < v then f (e w) else 0 := by
      apply Finset.sum_congr rfl
      intro w _hw
      have hcut : (e w).val < (e v).val ↔ w < v := by
        change e w < e v ↔ w < v
        exact e.lt_iff_lt
      simp only [hcut]

end ReflexiveFixedPoints.FinitePrefix

end OAI
