import OAI.Probability.MatroidProphet.Residual.Statistics
import Mathlib.Data.Set.Card.Arithmetic

namespace OAI

namespace MatroidProphet
open Set Finset Pivots
variable {α B : Type*} [Fintype α] [Fintype B]

lemma exists_rankWitness (M : Matroid α) (hE : M.E = Set.univ) (A S : Set α) :
    ∃ Z : Set α, Z ⊆ S ∧ Z.ncard = conditionalRank M S A ∧ S ⊆ M.closure (A ∪ Z) := by
  obtain ⟨Z, hZ, hgen, hcard⟩ := exists_extension_generators M hE (M.closure A) S
    (M.closure (M.closure A ∪ S)) (Matroid.isFlat_closure (M := M) _) rfl
  refine ⟨Z, hZ.trans sdiff_subset, ?_, ?_⟩
  · simp only [natRank_closure] at hcard
    have hrank : natRank M (M.closure A ∪ S) = natRank M (A ∪ S) := by
      simp only [natRank, M.eRk_union_closure_left_eq]
    rw [hrank] at hcard
    have hr := conditionalRank_add_base M S A
    rw [union_comm S A] at hr
    omega
  · rw [M.closure_union_closure_left_eq, M.closure_union_closure_left_eq] at hgen
    rw [hgen]
    exact subset_union_right.trans (M.subset_closure _ (by simp [hE]))

lemma collect_disjoint_witnesses (W : B → Set α) (U : Finset α)
    (hW : ∀ b, W b ⊆ (U : Set α))
    (hdisj : Pairwise (fun b c => Disjoint (W b) (W c))) :
    ∃ Z : Finset α, Z ⊆ U ∧ Z.card ≤ ∑ b, (W b).ncard ∧
      ∃ β : Z → B, ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b := by
  classical
  let Z := (⋃ b, W b).toFinset
  have hmem (w : Z) : ∃ b, w.val ∈ W b := by
    exact mem_iUnion.mp (Set.mem_toFinset.mp w.property)
  let β : Z → B := fun w => (hmem w).choose
  have hβ (w : Z) : w.val ∈ W (β w) := (hmem w).choose_spec
  refine ⟨Z, ?_, ?_, β, ?_⟩
  · intro e he
    obtain ⟨b, hb⟩ := mem_iUnion.mp (Set.mem_toFinset.mp he)
    exact hW b hb
  · rw [show Z.card = (⋃ b, W b).ncard from (Set.ncard_eq_toFinset_card' _).symm]
    exact Set.ncard_iUnion_le_of_fintype W
  · intro b
    ext e
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← hw]
      exact hβ w
    · intro he
      let w : Z := ⟨e, Set.mem_toFinset.mpr (mem_iUnion.mpr ⟨b, he⟩)⟩
      have heq : β w = b := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisj hne) (hβ w) he
      exact ⟨w, heq, rfl⟩

lemma residualUnion_subset_mask
    {α : Type u_1} {B : Type u_2} [Fintype α] [Fintype B]
    (M : Matroid α) (P A W : B → Set α) (O : Set α)
    (hspan : ∀ b, P b \ O ⊆ M.closure (A b ∪ W b)) :
    (⋃ b, P b \ M.closure (A b ∪ W b)) ⊆ O := by
  intro e he
  obtain ⟨b, hb⟩ := mem_iUnion.mp he
  by_contra hn
  exact hb.2 (hspan b ⟨hb.1, hn⟩)

lemma residualUnion_ncard (M : Matroid α) (P A W : B → Set α)
    (hdisj : Pairwise (fun b c => Disjoint (P b) (P c))) :
    (⋃ b, P b \ M.closure (A b ∪ W b)).ncard =
      ∑ b, (P b \ M.closure (A b ∪ W b)).ncard := by
  have hd : Pairwise (fun b c => Disjoint (P b \ M.closure (A b ∪ W b))
      (P c \ M.closure (A c ∪ W c))) := by
    intro b c hbc
    exact (hdisj hbc).mono sdiff_subset sdiff_subset
  simpa only [finsum_eq_sum_of_fintype] using Set.ncard_iUnion_of_finite (fun b => Set.toFinite _) hd

lemma nominal_rank_witnesses (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (h : ℕ) (U : Finset α) (O : Set α) (ε : Fin 2) :
    ∃ W : ParityWindow (activation h) ε → Set α,
      (∀ b, W b ⊆ nominalLayerSet M hE κ D C h (U : Set α) ε b \ O) ∧
      (∑ b, (W b).ncard) = nominalRankStatistic M hE κ D C T h (U : Set α) O ε ∧
      (∀ b, nominalLayerSet M hE κ D C h (U : Set α) ε b \ O ⊆
        M.closure ((nominalPath M hE κ D C h (b.val.val - 2) ∪
          lowerCompetition M hE κ D C T b.val.val h) ∪ W b)) ∧
      ∃ Z : Finset α, Z ⊆ U ∧ Z.card ≤ nominalRankStatistic M hE κ D C T h (U : Set α) O ε ∧
        ∃ β : Z → ParityWindow (activation h) ε,
          ∀ b, (fun w : Z => w.val) '' {w | β w = b} = W b := by
  classical
  choose W hW hc hs using fun b : ParityWindow (activation h) ε => exists_rankWitness M hE
    (nominalPath M hE κ D C h (b.val.val - 2) ∪ lowerCompetition M hE κ D C T b.val.val h)
    (nominalLayerSet M hE κ D C h (U : Set α) ε b \ O)
  have heq : (∑ b, (W b).ncard) = nominalRankStatistic M hE κ D C T h (U : Set α) O ε := by
    unfold nominalRankStatistic
    exact sum_congr rfl (fun b _ => hc b)
  have hd : Pairwise (fun b c => Disjoint (W b) (W c)) := by
    intro b c hbc
    exact (nominalLayerSet_disjoint M hE κ D C h (U : Set α) ε hbc).mono
      ((hW b).trans sdiff_subset) ((hW c).trans sdiff_subset)
  obtain ⟨Z, hZU, hZcard, β, hβ⟩ := collect_disjoint_witnesses W U
    (fun b => ((hW b).trans sdiff_subset).trans (nominalLayerSet_subset M hE κ D C h _ ε b)) hd
  refine ⟨W, hW, heq, hs, Z, hZU, ?_, β, hβ⟩
  rwa [heq] at hZcard

end MatroidProphet

end OAI
