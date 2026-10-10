import Mathlib

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace BernoulliCandidates
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq A]

/-- A convenient subset of the actual fieldwise-injective candidates consists
of globally injective free values avoiding every pinned letter. This is only a
lower bound; the actual candidate set does not prohibit cross-field coincidences. -/
lemma card_lower_of_embeddings (C : Finset (V → A)) (B : Finset A)
    (hC : ∀ f : V ↪ {a : A // a ∉ B}, (fun v => (f v).val) ∈ C) :
    ((Fintype.card A - B.card).descFactorial (Fintype.card V)) ≤ C.card := by
  classical
  have hi : Function.Injective (fun f : V ↪ {a : A // a ∉ B} =>
      (⟨fun v => (f v).val, hC f⟩ : C)) := by
    intro f g h
    apply DFunLike.ext
    intro v
    exact Subtype.ext (congrFun (congrArg Subtype.val h) v)
  have hh := Fintype.card_le_of_injective _ hi
  rw [Fintype.card_embedding_eq] at hh
  have hb : Fintype.card {a : A // a ∉ B} = Fintype.card A - B.card := by
    simp
  simpa only [hb, Fintype.card_coe] using hh

lemma real_descFactorial_lower (N b v : ℕ) (h : 2 * (b + v) ≤ N) :
    ((N : ℝ) / 2) ^ v ≤ ((N - b).descFactorial v : ℝ) := by
  have hb : b ≤ N := by omega
  have hnv : v ≤ N - b + 1 := by omega
  have hs : (N : ℝ) / 2 ≤ (N - b + 1 - v : ℕ) := by
    rw [Nat.cast_sub hnv, Nat.cast_add, Nat.cast_sub hb]
    push_cast
    have h' : (2 : ℝ) * (b + v) ≤ N := by exact_mod_cast h
    linarith
  exact (pow_le_pow_left₀ (by positivity) hs v).trans
    (by exact_mod_cast (N - b).pow_sub_le_descFactorial v)

lemma card_lower_half (C : Finset (V → A)) (B : Finset A)
    (hC : ∀ f : V ↪ {a : A // a ∉ B}, (fun v => (f v).val) ∈ C)
    (h : 2 * (B.card + Fintype.card V) ≤ Fintype.card A) :
    ((Fintype.card A : ℝ) / 2) ^ Fintype.card V ≤ C.card := by
  exact (real_descFactorial_lower _ _ _ h).trans
    (by exact_mod_cast card_lower_of_embeddings C B hC)

end BernoulliCandidates
end HyperbolicObstruction
end
end

section

end
end

end OAI
