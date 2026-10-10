import OAI.Probability.MatroidProphet.LayerGreedy

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma natRank_le_ncard (M : Matroid α) (S : Set α) : natRank M S ≤ S.ncard := by
  have h := ENat.toNat_le_toNat (M.eRk_le_encard S) (Set.toFinite S).encard_lt_top.ne
  simpa only [natRank, Set.ncard_def] using h

lemma conditionalRank_mono_left (M : Matroid α) (P : Set α)
    {S T : Set α} (hST : S ⊆ T) : conditionalRank M S P ≤ conditionalRank M T P := by
  exact Nat.sub_le_sub_right (natRank_mono M (union_subset_union_left P hST)) _

lemma conditionalRank_spanned (M : Matroid α) (hE : M.E = Set.univ)
    (S P H : Set α) (hspan : S ⊆ M.closure (P ∪ H)) :
    conditionalRank M S P ≤ H.ncard := by
  have hP : P ⊆ M.closure (P ∪ H) :=
    subset_union_left.trans (M.subset_closure _ (by simp [hE]))
  have hr := natRank_mono M (union_subset hspan hP)
  rw [natRank_closure] at hr
  have ht : conditionalRank M S P ≤ conditionalRank M H P := by
    unfold conditionalRank
    rw [union_comm H P]
    exact Nat.sub_le_sub_right hr _
  exact ht.trans ((conditionalRank_le_rank M H P).trans (natRank_le_ncard M H))

theorem layerGreedy_rank_lower (M : Matroid α) (hE : M.E = Set.univ)
    (E : Finset α) (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (b : ℤ) (S K : Set α) (high : α → Prop) [DecidablePred high]
    (hS : S \ base b ⊆ {e | e ∈ E ∧ layer e = b})
    (hK : ∀ e ∈ layerGreedy M E base layer time, layer e = b → ¬ high e → e ∈ K) :
    conditionalRank M S (base b ∪ K) ≤
      ((layerGreedy M E base layer time).filter (fun e => layer e = b ∧ high e)).card := by
  classical
  let H := (layerGreedy M E base layer time).filter (fun e => layer e = b ∧ high e)
  have hspan : S ⊆ M.closure ((base b ∪ K) ∪ (H : Set α)) := by
    intro e he
    by_cases heF : e ∈ base b
    · exact M.mem_closure_of_mem (Or.inl (Or.inl heF)) (by simp [hE])
    have hel := hS ⟨he, heF⟩
    have hs := layerGreedy_spans M E base layer time hE b hel
    apply M.closure_subset_closure ?_ hs
    rintro f (hf | ⟨hf, hb⟩)
    · exact Or.inl (Or.inl hf)
    · by_cases hh : high f
      · exact Or.inr (mem_filter.mpr ⟨hf, hb, hh⟩)
      · exact Or.inl (Or.inr (hK f hf hb hh))
  have hc := conditionalRank_spanned M hE S (base b ∪ K) (H : Set α) hspan
  simpa only [Set.ncard_coe_finset, H] using hc

theorem layerGreedy_sum_rank_lower [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (E : Finset α) (base : ℤ → Set α) (layer : α → ℤ) (time : α → ℕ)
    (points : Finset ℤ) (S K : ℤ → Set α) (high : α → Prop) [DecidablePred high]
    (hS : ∀ b ∈ points, S b \ base b ⊆ {e | e ∈ E ∧ layer e = b})
    (hK : ∀ b ∈ points, ∀ e ∈ layerGreedy M E base layer time,
      layer e = b → ¬ high e → e ∈ K b) :
    (∑ b ∈ points, conditionalRank M (S b) (base b ∪ K b)) ≤
      ((layerGreedy M E base layer time).filter high).card := by
  classical
  let A := layerGreedy M E base layer time
  calc
    _ ≤ ∑ b ∈ points, (A.filter (fun e => layer e = b ∧ high e)).card := by
      exact Finset.sum_le_sum fun b hb =>
        layerGreedy_rank_lower M hE E base layer time b (S b) (K b) high (hS b hb) (hK b hb)
    _ = ∑ b ∈ points, ((A.filter high).filter (fun e => layer e = b)).card := by
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      ext e
      simp only [Finset.mem_filter]
      tauto
    _ = ((A.filter high).filter (fun e => layer e ∈ points)).card :=
      Finset.sum_card_fiberwise_eq_card_filter (A.filter high) points layer
    _ ≤ (A.filter high).card := Finset.card_filter_le _ _

end MatroidProphet

end OAI
