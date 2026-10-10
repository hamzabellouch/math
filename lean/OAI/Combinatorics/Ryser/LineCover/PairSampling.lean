import OAI.Combinatorics.Ryser.LineCover.InjectionSampling
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace RyserCoveringCounterexample.InjectionSampling

theorem card_disjoint_pair_assignments_le
    {Ω : Type*} [Fintype Ω] (B : Finset (Ω × Ω)) (h : ℕ) :
    Fintype.card {u : (Fin h ⊕ Fin h) ↪ Ω //
      ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B} ≤ B.card ^ h := by
  classical
  let encode : {u : (Fin h ⊕ Fin h) ↪ Ω //
      ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B} → (Fin h → ↥B) :=
    fun u k => ⟨(u.val (Sum.inl k), u.val (Sum.inr k)), u.property k⟩
  have hencode : Function.Injective encode := by
    intro u v huv
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    cases slot with
    | inl k => exact congrArg (fun f : Fin h → ↥B => (f k).val.1) huv
    | inr k => exact congrArg (fun f : Fin h → ↥B => (f k).val.2) huv
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hencode

theorem prob_disjoint_pairs_le
    {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty (I ↪ Ω)]
    {h : ℕ} (j : (Fin h ⊕ Fin h) ↪ I) (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform (I ↪ Ω)).prob
        (fun u => ∀ k, (u (j (Sum.inl k)), u (j (Sum.inr k))) ∈ B) ≤
      (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  classical
  let : Nonempty ((Fin h ⊕ Fin h) ↪ Ω) :=
    ⟨j.trans (Classical.choice (inferInstance : Nonempty (I ↪ Ω)))⟩
  let P : ((Fin h ⊕ Fin h) ↪ Ω) → Prop :=
    fun u => ∀ k, (u (Sum.inl k), u (Sum.inr k)) ∈ B
  change (FiniteLaw.uniform (I ↪ Ω)).prob (fun u => P (restrict j u)) ≤ _
  rw [prob_restrict j P, FiniteLaw.uniform_prob]
  have hfilter :
      @Finset.filter _ P (fun sample => Classical.propDecidable (P sample))
          Finset.univ = Finset.univ.filter P :=
    Finset.filter_congr_decidable _ _ _
  rw [hfilter]
  have hnat : (Finset.univ.filter P).card ≤ B.card ^ h := by
    simpa only [Fintype.card_subtype] using card_disjoint_pair_assignments_le B h
  have hreal : ((Finset.univ.filter P).card : ℝ) ≤ ((B.card ^ h : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  rw [Nat.cast_pow] at hreal
  calc
    _ ≤ (B.card : ℝ) ^ h / Fintype.card ((Fin h ⊕ Fin h) ↪ Ω) :=
      div_le_div_of_nonneg_right hreal (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Fintype.card_embedding_eq, Fintype.card_sum, Fintype.card_fin,
        ← Nat.two_mul]

theorem prob_exists_disjoint_pairs_descFactorial_le
    {Ω : Type*} [Fintype Ω] {h t : ℕ}
    [Nonempty ((Fin t ⊕ Fin t) ↪ Ω)] (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)).prob
        (fun u => ∃ left right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) ≤
      (t.descFactorial h : ℝ) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  classical
  let μ := FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)
  calc
    _ ≤ ∑ left : Fin h ↪ Fin t,
        μ.prob (fun u => ∃ right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) :=
      μ.prob_exists_le _
    _ ≤ ∑ left : Fin h ↪ Fin t, ∑ right : Fin h ↪ Fin t,
        μ.prob (fun u =>
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) := by
      apply Finset.sum_le_sum
      intro left _
      exact μ.prob_exists_le _
    _ ≤ ∑ _left : Fin h ↪ Fin t, ∑ _right : Fin h ↪ Fin t,
        (B.card : ℝ) ^ h /
          ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
      apply Finset.sum_le_sum
      intro left _
      apply Finset.sum_le_sum
      intro right _
      exact prob_disjoint_pairs_le (Function.Embedding.sumMap left right) B
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin]
      ring

theorem prob_exists_disjoint_pairs_le
    {Ω : Type*} [Fintype Ω] {h t : ℕ}
    [Nonempty ((Fin t ⊕ Fin t) ↪ Ω)] (B : Finset (Ω × Ω)) :
    (FiniteLaw.uniform ((Fin t ⊕ Fin t) ↪ Ω)).prob
        (fun u => ∃ left right : Fin h ↪ Fin t,
          ∀ k, (u (Sum.inl (left k)), u (Sum.inr (right k))) ∈ B) ≤
      (t : ℝ) ^ (2 * h) * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
  have hslots : (t.descFactorial h : ℝ) ≤ (t : ℝ) ^ h := by
    have hcast : (t.descFactorial h : ℝ) ≤ ((t ^ h : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.descFactorial_le_pow t h)
    simpa only [Nat.cast_pow] using hcast
  calc
    _ ≤ (t.descFactorial h : ℝ) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) :=
      prob_exists_disjoint_pairs_descFactorial_le B
    _ ≤ ((t : ℝ) ^ h) ^ 2 * (B.card : ℝ) ^ h /
        ((Fintype.card Ω).descFactorial (2 * h) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hslots 2)
        (pow_nonneg (Nat.cast_nonneg _) h)
    _ = _ := by rw [← pow_mul, Nat.mul_comm h 2]

end RyserCoveringCounterexample.InjectionSampling

end

end OAI
