import OAI.Combinatorics.InfiniteMatroid.Zones

namespace OAI

section
open Set Filter
open scoped Topology symmDiff
namespace InfiniteMatroidCounterexample
namespace RankModel

variable (R : RankModel D) (hK : R.ideal = KIdeal)
include hK

lemma insert_prototype {ι : Type} (hι : Cardinal.mk ι < Cardinal.continuum)
    (T : ι → Set E0) {A Z : Set E0} (hAZ : A ⊆ Z)
    (hA : ¬ R.Upper A) (hZ : ¬ R.Lower Z)
    (hTA : ∀ i, ¬ Small (T i \ A)) (hZT : ∀ i, ¬ Small (Z \ T i)) :
    ∃ B, A ⊆ B ∧ B ⊆ Z ∧ R.Admissible B ∧
      ∀ i, ¬ Small (B \ T i) ∧ ¬ Small (T i \ B) := by
  classical
  let G := Z \ A
  let S0 (i : ι) : Set E0 := if Small (A \ T i) then G \ T i else Z \ T i
  let S1 (i : ι) : Set E0 := if Small (T i \ Z) then T i ∩ G else T i \ A
  have h0 (i : ι) : ¬ Small (S0 i) := by
    dsimp only [S0]
    split_ifs with hs
    · intro hg
      apply hZT i
      apply small_subset (small_union hs hg)
      intro x hx
      change x ∈ (A \ T i) ∪ ((Z \ A) \ T i)
      simp only [Set.mem_union,Set.mem_sdiff] at hx ⊢
      tauto
    · exact hZT i
  have h1 (i : ι) : ¬ Small (S1 i) := by
    dsimp only [S1]
    split_ifs with hs
    · intro hg
      apply hTA i
      apply small_subset (small_union hs hg)
      intro x hx
      change x ∈ (T i \ Z) ∪ (T i ∩ (Z \ A))
      simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff] at hx ⊢
      tauto
    · exact hTA i
  let traces (p : ι × Bool) : Set E0 := if p.2 then S1 p.1 else S0 p.1
  have ht : ∀ p, ¬ Small (traces p) := by
    rintro ⟨i,b⟩; cases b
    · exact h0 i
    · exact h1 i
  obtain ⟨t,hres⟩ := simultaneous_reservations (cardinal_prod_bool_lt hι) traces ht
  have hr0 (i : ι) : ¬ Small (S0 i ∩ HCell t false) := hres (i,false) false
  have hr1 (i : ι) : ¬ Small (S1 i ∩ HCell t true) := hres (i,true) true
  let A' := A ∪ (HCell t false ∩ G)
  let Z' := Z \ (HCell t true ∩ G)
  have hAA : A ⊆ A' := Set.subset_union_left
  have hZZ : Z' ⊆ Z := Set.sdiff_subset
  have hAZ' : A' ⊆ Z' := by
    intro x hx
    refine ⟨?_,?_⟩
    · rcases hx with hx | hx
      · exact hAZ hx
      · exact hx.2.1
    · intro hh
      rcases hx with hx | hx
      · exact hh.2.2 hx
      · exact Set.disjoint_left.mp (hCell_disjoint t) hx.1 hh.1
  have haInv : KSmall0 (A ∆ A') := by
    apply kSmall0_mono (hCell_kSmall0 t false)
    intro x hx
    change x ∈ A ∆ (A ∪ (HCell t false ∩ G)) at hx
    simp only [Set.mem_symmDiff,Set.mem_union,Set.mem_inter_iff] at hx
    tauto
  have hzInv : KSmall0 (Z ∆ Z') := by
    apply kSmall0_mono (hCell_kSmall0 t true)
    intro x hx
    change x ∈ Z ∆ (Z \ (HCell t true ∩ G)) at hx
    simp only [Set.mem_symmDiff,Set.mem_sdiff,Set.mem_inter_iff] at hx
    tauto
  have haU : ¬ R.Upper A' := ((R.status_invariant hK haInv).1).not.mp hA
  have hzL : ¬ R.Lower Z' := ((R.status_invariant hK hzInv).2.1).not.mp hZ
  obtain ⟨B,hAB,hBZ,hB⟩ := R.exists_admissible_between hAZ' haU hzL
  refine ⟨B,hAA.trans hAB,hBZ.trans hZZ,hB,fun i ↦ ⟨?_,?_⟩⟩
  · by_cases hs : Small (A \ T i)
    · have hr : ¬ Small ((G \ T i) ∩ HCell t false) := by simpa only [S0,ite_eq_left hs] using hr0 i
      intro hbad
      apply hr
      apply small_subset hbad
      intro x hx
      exact ⟨hAB (Or.inr ⟨hx.2,hx.1.1⟩),hx.1.2⟩
    · exact fun hb ↦ hs (small_subset hb (Set.sdiff_subset_sdiff_left (hAA.trans hAB)))
  · by_cases hs : Small (T i \ Z)
    · have hr : ¬ Small ((T i ∩ G) ∩ HCell t true) := by simpa only [S1,ite_eq_left hs] using hr1 i
      intro hbad
      apply hr
      apply small_subset hbad
      intro x hx
      exact ⟨hx.1.1,fun hxB ↦ (hBZ hxB).2 ⟨hx.2,hx.1.2⟩⟩
    · exact fun hb ↦ hs (small_subset hb (Set.sdiff_subset_sdiff_right (hBZ.trans hZZ)))

end RankModel
end InfiniteMatroidCounterexample
end

end OAI
