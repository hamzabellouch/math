import OAI.Probability.MatroidProphet.PathRankCost
import OAI.Probability.MatroidProphet.Residual.Timeline

namespace OAI

namespace MatroidProphet
open Set Finset

lemma sum_spaced_potential_drop (p : ℤ → ℕ) (hp : Antitone p)
    (L : Finset ℤ) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo + 2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b + 2 ≤ c) :
    (∑ b ∈ L, (p (b-2) - p b)) + p hi ≤ p lo := by
  induction L using Finset.induction_on_max generalizing lo hi with
  | empty => simpa using hp hlohi
  | @insert a L hmax ih =>
    have ha : a ∉ L := fun hm => (lt_irrefl a) (hmax a hm)
    have hla : lo ≤ a-2 := by have := hlo a (mem_insert_self a L); omega
    have harest : ∀ b ∈ L, b ≤ a-2 := by
      intro b hb
      have hb' := hmax b hb
      have hg := hgap b (mem_insert_of_mem hb) a (mem_insert_self a L) hb'
      omega
    have hrec := ih lo (a-2) hla
      (fun b hb => hlo b (mem_insert_of_mem hb)) harest
      (fun b hb c hc hbc => hgap b (mem_insert_of_mem hb) c (mem_insert_of_mem hc) hbc)
    have hahi := hhi a (mem_insert_self a L)
    have hphi := hp hahi
    have hpaa := hp (show a-2 ≤ a by omega)
    rw [sum_insert ha]
    omega

variable {α : Type*} [Fintype α]

theorem rankCost_spaced (M : Matroid α) (J : Set α) (L : Finset ℤ)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo+2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b+2 ≤ c)
    (X A B S : ℤ → Set α) (hX : Monotone X)
    (hXA : ∀ b ∈ L, X (b-2) ⊆ A b)
    (hAB : ∀ b ∈ L, A b ⊆ B b)
    (hB : ∀ b ∈ L, B b ⊆ M.closure (A b ∪ J))
    (hY : ∀ b ∈ L, A b ∪ S b ⊆ X b) :
    (∑ b ∈ L, conditionalRank M (S b) (A b)) ≤
      (∑ b ∈ L, conditionalRank M (S b) (B b)) + natRank M J := by
  have hp : Antitone (fun b => conditionalRank M J (X b)) :=
    fun _ _ hab => conditionalRank_antitone M J (hX hab)
  have hd := sum_spaced_potential_drop _ hp L lo hi hlohi hlo hhi hgap
  have hs : (∑ b ∈ L, conditionalRank M (S b) (A b)) ≤
      ∑ b ∈ L, (conditionalRank M (S b) (B b) +
        (conditionalRank M J (X (b-2)) - conditionalRank M J (X b))) := by
    apply sum_le_sum
    intro b hb
    have hc := rankCost_step M J (S b) (A b) (B b) (X (b-2)) (X b)
      (hXA b hb) (hAB b hb) (hB b hb) (hY b hb)
    have hm := conditionalRank_antitone M (S b) (hAB b hb)
    omega
  rw [sum_add_distrib] at hs
  have hb := conditionalRank_le_rank M J (X lo)
  omega

theorem actual_path_rank_cost_finset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later : ℕ)
    (L : Finset ℤ) (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hlo : ∀ b ∈ L, lo+2 ≤ b) (hhi : ∀ b ∈ L, b ≤ hi)
    (hgap : ∀ b ∈ L, ∀ c ∈ L, b < c → b+2 ≤ c)
    (S : ℤ → Set α) (hS : ∀ b, S b ⊆ nominalPath M hE κ D C h b) :
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)) ≤
    κ * (∑ b ∈ L, conditionalRank M (S b)
      (guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)) +
      κ * (C h).ncard +
        ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  obtain ⟨J, hJcost, hJ⟩ := exists_commonPathBudget M hE κ hκ D C h later
  have hXfinal (b : ℤ) : nominalPath M hE κ D C h b ⊆
      guardedPath M hE κ D C (h+1+later) b := by
    apply (nominal_subset_guarded M hE κ D C h b).trans
    have hm : Monotone (fun j => guardedPath M hE κ D C j b) :=
      monotone_nat_of_le_succ (fun j => (guarded_subset_nominal M hE κ D C j b).trans
        (nominal_subset_guarded M hE κ D C j b))
    exact hm (by omega)
  have hr := rankCost_spaced M J L lo hi hlohi hlo hhi hgap
    (nominalPath M hE κ D C h)
    (fun b => nominalPath M hE κ D C h (b-2) ∪ lowerCompetition M hE κ D C T b h)
    (fun b => guardedPath M hE κ D C (h+1+later) (b-2) ∪ lowerCompetition M hE κ D C T b h)
    S (nominalPath_mono M hE κ D C h)
    (fun _ _ => Set.subset_union_left)
    (fun b _ => Set.union_subset_union_left _ (hXfinal _))
    (by
      intro b hb
      apply Set.union_subset
      · exact (hJ _).trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl (Or.inl he)
          · exact Or.inr he))
      · intro e he
        exact M.mem_closure_of_mem (Or.inl (Or.inr he)) (by simp [hE]))
    (by
      intro b hb
      apply Set.union_subset
      · apply Set.union_subset
        · exact nominalPath_mono M hE κ D C h (by omega)
        · exact (lowerCompetition_subset_guarded M hE κ D C T _ h).trans
            (guarded_subset_nominal M hE κ D C h _)
      · exact hS _)
  have hmul := Nat.mul_le_mul_left κ hr
  rw [Nat.mul_add] at hmul
  have hcard := natRank_le_ncard M J
  have hbound := (Nat.mul_le_mul_left κ hcard).trans hJcost
  omega

noncomputable def parityPoints (a : ℤ) (ε : Fin 2) : Finset ℤ :=
  Finset.univ.image (fun b : Pivots.ParityWindow a ε => b.val.val)

lemma mem_parityPoints (a : ℤ) (ε : Fin 2) (b : ℤ) :
    b ∈ parityPoints a ε ↔ a-2 ≤ b ∧ b ≤ 1 ∧ b % 2 = (ε.val : ℤ) := by
  classical
  constructor
  · intro hb
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨c.val.property.1, c.val.property.2, c.property⟩
  · rintro ⟨hl, hr, hm⟩
    exact Finset.mem_image.mpr ⟨⟨⟨b, ⟨hl, hr⟩⟩, hm⟩, Finset.mem_univ _, rfl⟩

lemma sum_parityPoints {β : Type*} [AddCommMonoid β] (a : ℤ) (ε : Fin 2) (f : ℤ → β) :
    (∑ b ∈ parityPoints a ε, f b) = ∑ b : Pivots.ParityWindow a ε, f b.val.val := by
  classical
  apply Finset.sum_image
  intro x _ y _ hxy
  exact Subtype.ext (Subtype.ext hxy)

end MatroidProphet

end OAI
