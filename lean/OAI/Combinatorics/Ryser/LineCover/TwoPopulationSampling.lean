import OAI.Combinatorics.Ryser.LineCover.InjectionSampling
import OAI.Combinatorics.Ryser.Probability.Product
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace RyserCoveringCounterexample

namespace InjectionSampling

theorem card_pairSample_relation_le
    {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A × B)) (h : ℕ) :
    Fintype.card {z : (Fin h ↪ A) × (Fin h ↪ B) //
      ∀ i, (z.1 i, z.2 i) ∈ S} ≤ S.card ^ h := by
  classical
  let enc : {z : (Fin h ↪ A) × (Fin h ↪ B) //
      ∀ i, (z.1 i, z.2 i) ∈ S} → (Fin h → ↥S) :=
    fun z i => ⟨(z.val.1 i, z.val.2 i), z.property i⟩
  have hinj : Function.Injective enc := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun f : Fin h → ↥S => (f i).val.1) hzw
    · apply Function.Embedding.ext
      intro i
      exact congrArg (fun f : Fin h → ↥S => (f i).val.2) hzw
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective enc hinj

theorem prob_restrict_product
    {A B I J K L : Type*}
    [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty (J ↪ A)] [Nonempty (I ↪ A)]
    [Nonempty (L ↪ B)] [Nonempty (K ↪ B)]
    (i : I ↪ J) (j : K ↪ L) (P : (I ↪ A) × (K ↪ B) → Prop) :
    ((FiniteLaw.uniform (J ↪ A)).prod (FiniteLaw.uniform (L ↪ B))).prob
        (fun z => P (restrict i z.1, restrict j z.2)) =
      ((FiniteLaw.uniform (I ↪ A)).prod (FiniteLaw.uniform (K ↪ B))).prob P := by
  rw [FiniteLaw.prob_prod_average, FiniteLaw.prob_prod_average]
  calc
    _ = (FiniteLaw.uniform (J ↪ A)).expectation
        (fun a => (FiniteLaw.uniform (K ↪ B)).prob
          (fun b => P (restrict i a, b))) := by
      congr 1
      funext a
      exact prob_restrict j (fun b => P (restrict i a, b))
    _ = _ := by
      simpa only [FiniteLaw.expectation_map] using
        congrArg
          (fun mu : FiniteLaw (I ↪ A) => mu.expectation
            (fun a => (FiniteLaw.uniform (K ↪ B)).prob (fun b => P (a, b))))
          (map_uniform_restrict (Ω := A) i)

theorem prob_pairSample_relation_le
    {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset (A × B)) (h : ℕ)
    [Nonempty (Fin h ↪ A)] [Nonempty (Fin h ↪ B)] :
    ((FiniteLaw.uniform (Fin h ↪ A)).prod (FiniteLaw.uniform (Fin h ↪ B))).prob
        (fun z => ∀ i, (z.1 i, z.2 i) ∈ S) ≤
      (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  classical
  rw [← FiniteLaw.uniform_prod, FiniteLaw.uniform_prob]
  have hfilter :
      @Finset.filter _ (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
          ∀ i, (z.1 i, z.2 i) ∈ S)
        (fun z => Classical.propDecidable (∀ i, (z.1 i, z.2 i) ∈ S)) Finset.univ =
      Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
        ∀ i, (z.1 i, z.2 i) ∈ S) :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  have hnat : (Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
      ∀ i, (z.1 i, z.2 i) ∈ S)).card ≤ S.card ^ h := by
    simpa only [Fintype.card_subtype] using card_pairSample_relation_le S h
  have hreal : ((Finset.univ.filter (fun z : (Fin h ↪ A) × (Fin h ↪ B) =>
      ∀ i, (z.1 i, z.2 i) ∈ S)).card : ℝ) ≤ ((S.card ^ h : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_pow] at hreal
  simpa only [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_fin,
    Nat.cast_mul] using
    (div_le_div_of_nonneg_right hreal
      (Nat.cast_nonneg (Fintype.card ((Fin h ↪ A) × (Fin h ↪ B))) :
        (0 : ℝ) ≤ (Fintype.card ((Fin h ↪ A) × (Fin h ↪ B)) : ℝ)))

theorem prob_restricted_relation_le
    {A B : Type*} [Fintype A] [Fintype B] {h t : ℕ}
    [Nonempty (Fin t ↪ A)] [Nonempty (Fin h ↪ A)]
    [Nonempty (Fin t ↪ B)] [Nonempty (Fin h ↪ B)]
    (S : Finset (A × B)) (i j : Fin h ↪ Fin t) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).prob
        (fun z => ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) ≤
      (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  change ((FiniteLaw.uniform (Fin t ↪ A)).prod
      (FiniteLaw.uniform (Fin t ↪ B))).prob
      (fun z => (fun w : (Fin h ↪ A) × (Fin h ↪ B) =>
        ∀ k, (w.1 k, w.2 k) ∈ S) (restrict i z.1, restrict j z.2)) ≤ _
  rw [prob_restrict_product i j (fun w : (Fin h ↪ A) × (Fin h ↪ B) =>
    ∀ k, (w.1 k, w.2 k) ∈ S)]
  exact prob_pairSample_relation_le S h

theorem prob_relation_matching_le
    {A B : Type*} [Fintype A] [Fintype B] {h t : ℕ}
    [Nonempty (Fin t ↪ A)] [Nonempty (Fin h ↪ A)]
    [Nonempty (Fin t ↪ B)] [Nonempty (Fin h ↪ B)]
    (S : Finset (A × B)) :
    ((FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))).prob
        (fun z => ∃ i j : Fin h ↪ Fin t, ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) ≤
      (t.descFactorial h : ℝ) ^ 2 * (S.card : ℝ) ^ h /
        ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
  classical
  let mu := (FiniteLaw.uniform (Fin t ↪ A)).prod (FiniteLaw.uniform (Fin t ↪ B))
  calc
    _ ≤ ∑ i : Fin h ↪ Fin t,
        mu.prob (fun z => ∃ j : Fin h ↪ Fin t,
          ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) :=
      mu.prob_exists_le _
    _ ≤ ∑ i : Fin h ↪ Fin t, ∑ j : Fin h ↪ Fin t,
        mu.prob (fun z => ∀ k, (z.1 (i k), z.2 (j k)) ∈ S) := by
      apply Finset.sum_le_sum
      intro i _
      exact mu.prob_exists_le _
    _ ≤ ∑ _i : Fin h ↪ Fin t, ∑ _j : Fin h ↪ Fin t,
        (S.card : ℝ) ^ h /
          ((Fintype.card A).descFactorial h * (Fintype.card B).descFactorial h : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact prob_restricted_relation_le S i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin]
      ring

end InjectionSampling

end RyserCoveringCounterexample

end

end OAI
