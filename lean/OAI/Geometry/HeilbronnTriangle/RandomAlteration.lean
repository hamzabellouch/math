import OAI.Geometry.HeilbronnTriangle.SampleDeletion

namespace OAI


namespace Problem355.Alteration

theorem weighted_card_eq_sum {Ω α : Type*} [DecidableEq α] (outcomes : Finset Ω) (E : Finset α)
    (weight : Ω → ℝ) (A : Ω → Finset α)
    (hA : ∀ ω ∈ outcomes, A ω ⊆ E) :
    (∑ ω ∈ outcomes, weight ω * (A ω).card) =
      ∑ a ∈ E, ∑ ω ∈ outcomes, if a ∈ A ω then weight ω else 0 := by
  classical
  calc
    (∑ ω ∈ outcomes, weight ω * (A ω).card) =
        ∑ ω ∈ outcomes, ∑ a ∈ E, if a ∈ A ω then weight ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      have hfilter : E.filter (fun a => a ∈ A ω) = A ω := by
        ext a
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun ha => ⟨hA ω hω ha, ha⟩⟩
      have hcard : ((A ω).card : ℝ) = ∑ a ∈ E, if a ∈ A ω then 1 else 0 := by
        rw [Finset.sum_boole, hfilter]
      rw [hcard, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp
    _ = _ := Finset.sum_comm

theorem weighted_card_le {Ω α : Type*} [DecidableEq α] (outcomes : Finset Ω) (E : Finset α)
    (weight : Ω → ℝ) (A : Ω → Finset α) (bound : ℝ)
    (hA : ∀ ω ∈ outcomes, A ω ⊆ E)
    (hmarginal : ∀ a ∈ E,
      (∑ ω ∈ outcomes, if a ∈ A ω then weight ω else 0) ≤ bound) :
    (∑ ω ∈ outcomes, weight ω * (A ω).card) ≤ (E.card : ℝ) * bound := by
  classical
  rw [weighted_card_eq_sum outcomes E weight A hA]
  calc
    (∑ a ∈ E, ∑ ω ∈ outcomes, if a ∈ A ω then weight ω else 0) ≤
        ∑ _a ∈ E, bound := Finset.sum_le_sum hmarginal
    _ = _ := by simp

theorem exists_nat_lt_of_weighted_sum_lt {Ω : Type*} (outcomes : Finset Ω)
    (weight : Ω → ℝ) (g : Ω → ℕ) (m : ℕ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
    (hmean : (∑ ω ∈ outcomes, weight ω * g ω) < (m : ℝ)) :
    ∃ ω ∈ outcomes, g ω < m := by
  by_contra hnone
  push Not at hnone
  have hle : (m : ℝ) ≤ ∑ ω ∈ outcomes, weight ω * g ω := by
    calc
      (m : ℝ) = ∑ ω ∈ outcomes, weight ω * m := by
        rw [← Finset.sum_mul, hnorm, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun ω hω =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast hnone ω hω) (hweight ω hω)
  exact (not_lt_of_ge hle) hmean

theorem exists_good_sample_of_marginal_bounds {Ω ι β : Type*} [DecidableEq ι]
    (outcomes : Finset Ω) (weight : Ω → ℝ) (S : Finset ι)
    (f : Ω → ι → β) (bad : β → β → β → Prop) (n : ℕ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
    (hn : n ≤ S.card) (p q : ℝ)
    (hpair : ∀ e ∈ S.powersetCard 2,
      (∑ ω ∈ outcomes, if e ∈ collisionEdges S (f ω) then weight ω else 0) ≤ p)
    (htriple : ∀ e ∈ S.powersetCard 3,
      (∑ ω ∈ outcomes, if e ∈ badTripleEdges S (f ω) bad then weight ω else 0) ≤ q)
    (hsmall : (Nat.choose S.card 2 : ℝ) * p + (Nat.choose S.card 3 : ℝ) * q <
      ((S.card - n + 1 : ℕ) : ℝ)) :
    ∃ ω ∈ outcomes, ∃ T : Finset ι, T ⊆ S ∧ T.card = n ∧
      Set.InjOn (f ω) (T : Set ι) ∧
      ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
        i ≠ j → i ≠ k → j ≠ k → ¬ bad (f ω i) (f ω j) (f ω k) := by
  classical
  have hpairMean := weighted_card_le outcomes (S.powersetCard 2) weight
    (fun ω => collisionEdges S (f ω)) p
    (fun ω _ => Finset.filter_subset _ _) hpair
  have htripleMean := weighted_card_le outcomes (S.powersetCard 3) weight
    (fun ω => badTripleEdges S (f ω) bad) q
    (fun ω _ => Finset.filter_subset _ _) htriple
  simp only [Finset.card_powersetCard] at hpairMean htripleMean
  let g : Ω → ℕ := fun ω =>
    (collisionEdges S (f ω)).card + (badTripleEdges S (f ω) bad).card
  have hmean : (∑ ω ∈ outcomes, weight ω * g ω) < ((S.card - n + 1 : ℕ) : ℝ) := by
    calc
      (∑ ω ∈ outcomes, weight ω * g ω) =
          (∑ ω ∈ outcomes, weight ω * (collisionEdges S (f ω)).card) +
          (∑ ω ∈ outcomes, weight ω * (badTripleEdges S (f ω) bad).card) := by
        simp only [g, Nat.cast_add, mul_add, Finset.sum_add_distrib]
      _ ≤ (Nat.choose S.card 2 : ℝ) * p + (Nat.choose S.card 3 : ℝ) * q :=
        add_le_add hpairMean htripleMean
      _ < _ := hsmall
  obtain ⟨ω, hω, hg⟩ := exists_nat_lt_of_weighted_sum_lt outcomes weight g
    (S.card - n + 1) hweight hnorm hmean
  have hbudget : n + (collisionEdges S (f ω)).card +
      (badTripleEdges S (f ω) bad).card ≤ S.card := by
    dsimp [g] at hg
    omega
  obtain ⟨T, hTS, hcard, hinj, hgood⟩ :=
    exists_sample_subset_avoiding S (f ω) bad n hbudget
  exact ⟨ω, hω, T, hTS, hcard, hinj, hgood⟩

end Problem355.Alteration

end OAI
