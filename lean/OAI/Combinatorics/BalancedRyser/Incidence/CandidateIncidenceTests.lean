import OAI.Combinatorics.BalancedRyser.Candidates.CandidateSuccessfulAssembly

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open CandidateRetentionTransport

abbrev Test (F : Type*) :=
  Point F ⊕ ((Point F × Line F) ⊕ ((Line F × Line F) ⊕
    ((Direction F × Direction F) ⊕ (Direction F × Line F))))

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def count (M : MergedPairs F) : Test F → ℕ
  | Sum.inl p => (successfulTest M (fun A => p ∈ designated M A)).card
  | Sum.inr (Sum.inl (p, l)) =>
      if ¬ OnLine p l then
        (successfulTest M (fun A => OnLine p A.line ∧
          ∃ r ∈ designated M A, OnLine r l)).card else 0
  | Sum.inr (Sum.inr (Sum.inl (l, k))) =>
      if l ≠ k ∧ l ∉ constituentLines M ∧ k ∉ constituentLines M then
        (successfulTest M (fun A => ∃ p ∈ designated M A, ∃ r ∈ designated M A,
          p ≠ r ∧ OnLine p l ∧ OnLine r k)).card else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (d, e)))) =>
      if d ≠ e then
        (successfulTest M (fun A => ({d, e} : Finset (Direction F)) ⊆
          generatorSet A.tuple)).card else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (g, l)))) =>
      (successfulTest M (fun A => A.line.1 = g ∧
        ∃ p ∈ designated M A, OnLine p l)).card

omit [Field F] [DecidableEq F] in

theorem card_test : Fintype.card (Test F) =
    (Fintype.card F) ^ 2 +
    (Fintype.card F) ^ 3 * (Fintype.card F + 1) +
    (Fintype.card F) ^ 2 * (Fintype.card F + 1) ^ 2 +
    (Fintype.card F + 1) ^ 2 +
    Fintype.card F * (Fintype.card F + 1) ^ 2 := by
  simp only [Test, Point, Line, Direction, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_option]
  ring

omit [DecidableEq F] in

theorem card_test_le : Fintype.card (Test F) ≤ 15 * (Fintype.card F) ^ 4 := by
  rw [card_test]
  let q := Fintype.card F
  have hq : 1 ≤ q := Fintype.card_pos
  have h1 : q ≤ q ^ 2 := by nlinarith
  have h2 : q ^ 2 ≤ q ^ 3 := by
    nlinarith [Nat.mul_le_mul_left q h1]
  have h3 : q ^ 3 ≤ q ^ 4 := by
    nlinarith [Nat.mul_le_mul_left q h2]
  change q ^ 2 + q ^ 3 * (q + 1) + q ^ 2 * (q + 1) ^ 2 +
    (q + 1) ^ 2 + q * (q + 1) ^ 2 ≤ 15 * q ^ 4
  nlinarith

theorem count_le (M : MergedPairs F) (t : Test F) :
    count M t ≤ Fintype.card (SplitChoice F) := by
  rcases t with p | (⟨p,l⟩ | (⟨l,k⟩ | (⟨d,e⟩ | ⟨g,l⟩)))
  all_goals simp only [count]
  all_goals first | exact Finset.card_le_univ _ | split_ifs <;> first
    | exact Finset.card_le_univ _ | exact Nat.zero_le _

def SmallGood (M : MergedPairs F) (P : ℕ) : Prop := ∀ t : Test F, count M t ≤ P

theorem smallGood_iff (M : MergedPairs F) (P : ℕ) : SmallGood M P ↔
    (∀ p, (successfulTest M (fun A => p ∈ designated M A)).card ≤ P) ∧
    (∀ p l, ¬ OnLine p l →
      (successfulTest M (fun A => OnLine p A.line ∧
        ∃ r ∈ designated M A, OnLine r l)).card ≤ P) ∧
    (∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
      (successfulTest M (fun A => ∃ p ∈ designated M A, ∃ r ∈ designated M A,
        p ≠ r ∧ OnLine p l ∧ OnLine r k)).card ≤ P) ∧
    (∀ e : Finset (Direction F), e.card = 2 →
      (successfulTest M (fun A => e ⊆ generatorSet A.tuple)).card ≤ P) ∧
    (∀ g : Direction F, ∀ l : Line F,
      (successfulTest M (fun A => A.line.1 = g ∧
        ∃ p ∈ designated M A, OnLine p l)).card ≤ P) := by
  constructor
  · intro h
    refine ⟨fun p => h (Sum.inl p), ?_, ?_, ?_,
      fun g l => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (g,l)))))⟩
    · intro p l hp
      simpa only [count, ite_eq_left hp] using h (Sum.inr (Sum.inl (p,l)))
    · intro l k hne hl hk
      have hg : l ≠ k ∧ l ∉ constituentLines M ∧ k ∉ constituentLines M := ⟨hne, hl, hk⟩
      simpa only [count, ite_eq_left hg] using
        h (Sum.inr (Sum.inr (Sum.inl (l,k))))
    · intro e he
      obtain ⟨d, f, hdf, rfl⟩ := Finset.card_eq_two.mp he
      simpa only [count, ite_eq_left hdf] using
        h (Sum.inr (Sum.inr (Sum.inr (Sum.inl (d,f)))))
  · rintro ⟨hp, hpl, hll, hde, hgl⟩ t
    rcases t with p | (⟨p,l⟩ | (⟨l,k⟩ | (⟨d,e⟩ | ⟨g,l⟩)))
    · exact hp p
    · by_cases h : OnLine p l
      · simp [count, h]
      · simpa only [count, ite_eq_left h] using hpl p l h
    · simp only [count]
      split_ifs with h
      · exact hll l k h.1 h.2.1 h.2.2
      · exact Nat.zero_le P
    · simp only [count]
      split_ifs with h
      · exact hde {d,e} (by simp [h])
      · exact Nat.zero_le P
    · exact hgl g l

def GlobalGood (M : MergedPairs F) (C : ℝ) : Prop :=
  ∀ l : Line F, l ∉ constituentLines M →
    ((successfulTest M (fun A => ∃ p ∈ designated M A, OnLine p l)).card : ℝ) ≤
      C * Fintype.card F

def SizeGood (M : MergedPairs F) (c : ℝ) : Prop :=
  ∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ)

universe u

theorem exists_threshold_graphGood (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → ∀ (M : MergedPairs F) (c : ℝ),
      SizeGood M c →
      SmallGood M (Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))) →
      GlobalGood M C →
      (∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card F : ℝ))) →
      (∀ l : Line F, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) →
      CandidateGraphGood M c (2 * C + 11) := by
  obtain ⟨N, hN⟩ := exists_threshold_candidateGraphGood_of_successful_counts.{u} C hC
  refine ⟨N, ?_⟩
  intro F _ _ _ hq M c hsize hsmall hglobal hcap hocc
  obtain ⟨hp, hpl, hll, hde, hgl⟩ := (smallGood_iff M _).mp hsmall
  exact hN F hq M c hsize hp hpl hll hde hcap hgl hglobal hocc

end
end Balanced.CandidateIncidenceTests

end OAI
