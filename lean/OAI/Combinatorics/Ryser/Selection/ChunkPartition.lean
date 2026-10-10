import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Basic

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {E : Type*} [DecidableEq E]

noncomputable def chunkRank (T : Finset E) (e : E) : ℕ :=
  if h : e ∈ T then (T.equivFin ⟨e, h⟩).val else 0

def chunkCount (T : Finset E) (L : ℕ) : ℕ := T.card / L + 1

noncomputable def candidateChunk (T : Finset E) (L j : ℕ) : Finset E :=
  T.filter (fun e => chunkRank T e / L = j)

noncomputable def chunkPrefix (T : Finset E) (L j : ℕ) : Finset E :=
  T.filter (fun e => chunkRank T e / L < j)

@[simp] theorem chunkRank_of_mem (T : Finset E) (e : E) (he : e ∈ T) :
    chunkRank T e = (T.equivFin ⟨e, he⟩).val := by
  simp only [chunkRank, dite_eq_left he]

theorem chunkRank_lt_card (T : Finset E) (e : E) (he : e ∈ T) :
    chunkRank T e < T.card := by
  rw [chunkRank_of_mem T e he]
  exact (T.equivFin ⟨e, he⟩).isLt

theorem chunkRank_injOn (T : Finset E) : Set.InjOn (chunkRank T) (T : Set E) := by
  intro a ha b hb hab
  have hval : (T.equivFin ⟨a, ha⟩).val = (T.equivFin ⟨b, hb⟩).val := by
    simpa only [chunkRank_of_mem T a ha, chunkRank_of_mem T b hb] using hab
  exact congrArg Subtype.val ((T.equivFin).injective (Fin.ext hval))

@[simp] theorem mem_candidateChunk (T : Finset E) (L j : ℕ) (e : E) :
    e ∈ candidateChunk T L j ↔ e ∈ T ∧ chunkRank T e / L = j :=
  Finset.mem_filter

@[simp] theorem mem_chunkPrefix (T : Finset E) (L j : ℕ) (e : E) :
    e ∈ chunkPrefix T L j ↔ e ∈ T ∧ chunkRank T e / L < j :=
  Finset.mem_filter

theorem candidateChunk_subset (T : Finset E) (L j : ℕ) :
    candidateChunk T L j ⊆ T :=
  Finset.filter_subset _ _

theorem chunkPrefix_subset (T : Finset E) (L j : ℕ) :
    chunkPrefix T L j ⊆ T :=
  Finset.filter_subset _ _

theorem candidateChunk_disjoint (T : Finset E) (L : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (candidateChunk T L i) (candidateChunk T L j) := by
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hi := (mem_candidateChunk T L i e).mp hei
  have hj := (mem_candidateChunk T L j e).mp hej
  exact hij (hi.2.symm.trans hj.2)

theorem candidateChunk_pairwise_disjoint (T : Finset E) (L : ℕ) :
    Pairwise (fun i j : ℕ => Disjoint (candidateChunk T L i) (candidateChunk T L j)) := by
  intro i j hij
  exact candidateChunk_disjoint T L hij

theorem candidateChunk_card_le (T : Finset E) (L j : ℕ) (hL : 0 < L) :
    (candidateChunk T L j).card ≤ L := by
  calc
    (candidateChunk T L j).card ≤ (Finset.range L).card := by
      apply Finset.card_le_card_of_injOn (fun e => chunkRank T e % L)
      · intro e _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hL)
      · intro a ha b hb hab
        change chunkRank T a % L = chunkRank T b % L at hab
        obtain ⟨haT, haq⟩ := (mem_candidateChunk T L j a).mp ha
        obtain ⟨hbT, hbq⟩ := (mem_candidateChunk T L j b).mp hb
        apply chunkRank_injOn T haT hbT
        calc
          chunkRank T a = chunkRank T a % L + L * (chunkRank T a / L) :=
            (Nat.mod_add_div (chunkRank T a) L).symm
          _ = chunkRank T b % L + L * (chunkRank T b / L) := by
            rw [hab, haq, hbq]
          _ = chunkRank T b := Nat.mod_add_div (chunkRank T b) L
    _ = L := Finset.card_range L

@[simp] theorem chunkPrefix_zero (T : Finset E) (L : ℕ) :
    chunkPrefix T L 0 = ∅ := by
  ext e
  simp only [mem_chunkPrefix, Nat.not_lt_zero, and_false, Finset.notMem_empty]

theorem chunkPrefix_succ (T : Finset E) (L j : ℕ) :
    chunkPrefix T L (j + 1) = chunkPrefix T L j ∪ candidateChunk T L j := by
  ext e
  constructor
  · intro he
    obtain ⟨heT, hj⟩ := (mem_chunkPrefix T L (j + 1) e).mp he
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact Finset.mem_union.mpr (Or.inl ((mem_chunkPrefix T L j e).mpr ⟨heT, hlt⟩))
    · exact Finset.mem_union.mpr (Or.inr ((mem_candidateChunk T L j e).mpr ⟨heT, heq⟩))
  · intro he
    rcases Finset.mem_union.mp he with hp | hc
    · obtain ⟨heT, hlt⟩ := (mem_chunkPrefix T L j e).mp hp
      exact (mem_chunkPrefix T L (j + 1) e).mpr ⟨heT, Nat.lt_succ_of_lt hlt⟩
    · obtain ⟨heT, heq⟩ := (mem_candidateChunk T L j e).mp hc
      exact (mem_chunkPrefix T L (j + 1) e).mpr
        ⟨heT, Nat.lt_succ_iff_lt_or_eq.mpr (Or.inr heq)⟩

theorem disjoint_chunkPrefix_candidateChunk (T : Finset E) (L j : ℕ) :
    Disjoint (chunkPrefix T L j) (candidateChunk T L j) := by
  apply Finset.disjoint_left.mpr
  intro e hp hc
  have hlt := ((mem_chunkPrefix T L j e).mp hp).2
  have heq := ((mem_candidateChunk T L j e).mp hc).2
  exact (Nat.ne_of_lt hlt) heq

theorem chunkIndex_lt_count (T : Finset E) (L : ℕ) (e : E) (he : e ∈ T) :
    chunkRank T e / L < chunkCount T L := by
  exact Nat.lt_succ_of_le
    (Nat.div_le_div_right (Nat.le_of_lt (chunkRank_lt_card T e he)))

@[simp] theorem chunkPrefix_count (T : Finset E) (L : ℕ) :
    chunkPrefix T L (chunkCount T L) = T := by
  ext e
  constructor
  · exact fun he => ((mem_chunkPrefix T L (chunkCount T L) e).mp he).1
  · intro he
    exact (mem_chunkPrefix T L (chunkCount T L) e).mpr
      ⟨he, chunkIndex_lt_count T L e he⟩

theorem biUnion_candidateChunk (T : Finset E) (L : ℕ) :
    (Finset.range (chunkCount T L)).biUnion (candidateChunk T L) = T := by
  ext e
  constructor
  · intro he
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp he
    exact candidateChunk_subset T L j hj
  · intro he
    refine Finset.mem_biUnion.mpr ⟨chunkRank T e / L, ?_, ?_⟩
    · exact Finset.mem_range.mpr (chunkIndex_lt_count T L e he)
    · exact (mem_candidateChunk T L (chunkRank T e / L) e).mpr ⟨he, rfl⟩

end RyserCoveringCounterexample.Selection

end OAI
