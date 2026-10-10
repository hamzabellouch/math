import OAI.Combinatorics.ThinTrees.DyadicSelection

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

def nextIndex (I : Finset ℕ) (i z : ℕ) : ℕ :=
  if h : (I.filter (fun j => i < j)).Nonempty then (I.filter (fun j => i < j)).min' h else z

lemma nextIndex_spec {I : Finset ℕ} {i z : ℕ} (hz : z ∈ I) (hiz : i < z) :
    nextIndex I i z ∈ I ∧ i < nextIndex I i z ∧ ∀j ∈ I, i < j → nextIndex I i z ≤ j := by
  classical
  have h : (I.filter (fun j => i < j)).Nonempty := ⟨z,mem_filter.mpr ⟨hz,hiz⟩⟩
  rw [nextIndex,dite_eq_left h]
  have hm := min'_mem _ h
  exact ⟨(mem_filter.mp hm).1,(mem_filter.mp hm).2,fun j hj hij => min'_le _ _ (mem_filter.mpr ⟨hj,hij⟩)⟩

lemma transition_bad_bound {I : Finset ℕ} {H : Hierarchy n} (hH : H.nodes=P.nodes I)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (hij : i < j)
    (hnext : ∀k ∈ I, i < k → j ≤ k) (Bad : Finset (Fin m)) {c : ℝ} (hc : 0 ≤ c)
    (hnode : ∀A ∈ H.nodes, ((Bad ∩ H.parentBoundary G A).card : ℝ) ≤ c*(G.cut univ A).card) :
    ((Bad ∩ (P.crossing G i \ P.crossing G j)).card : ℝ) ≤ 2*c*(P.crossing G i).card := by
  classical
  have hs : Bad ∩ (P.crossing G i \ P.crossing G j) ⊆
      (P.parts i).biUnion (fun A => Bad ∩ H.parentBoundary G A) := by
    intro e he
    obtain ⟨hBad,hc⟩ := mem_inter.mp he
    obtain ⟨A,hA,heA⟩ := P.disappearing_in_parentBoundary G hH hi hj hij hnext hc
    exact mem_biUnion.mpr ⟨A,hA,mem_inter.mpr ⟨hBad,heA⟩⟩
  have hh := (card_le_card hs).trans (card_biUnion_le)
  calc
    ((Bad ∩ (P.crossing G i \ P.crossing G j)).card : ℝ) ≤
        ∑A ∈ P.parts i, ((Bad ∩ H.parentBoundary G A).card : ℝ) := by exact_mod_cast hh
    _ ≤ ∑A ∈ P.parts i, c*(G.cut univ A).card := by
      apply sum_le_sum
      intro A hA
      exact hnode A (hH ▸ P.mem_nodes.mpr (Or.inl ⟨i,hi,hA⟩))
    _ = c*(∑A ∈ P.parts i, (G.cut univ A).card : ℕ) := by rw [Nat.cast_sum,mul_sum]
    _ ≤ c*(2*(P.crossing G i).card) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact_mod_cast P.boundary_sum_le G i
    _ = _ := by ring

lemma selected_lt_end {z i : ℕ} (hz : P.parts z={univ})
    (hi : i ∈ Dyadic.selected (fun j => (P.crossing G j).card) z) : i < z := by
  obtain ⟨hiz,hip,_⟩ := Dyadic.selected_spec hi
  have hzero : (P.crossing G z).card=0 := by rw [P.crossing_root G hz,card_empty]
  apply lt_of_le_of_ne hiz
  intro he
  subst i
  omega

lemma selected_tail_bad_bound {z : ℕ} (hz : P.parts z={univ})
    {H : Hierarchy n}
    (hH : H.nodes=P.nodes (insert z (Dyadic.selected (fun j => (P.crossing G j).card) z)))
    (Bad : Finset (Fin m)) {c : ℝ} (hc : 0 ≤ c)
    (hnode : ∀A ∈ H.nodes, ((Bad ∩ H.parentBoundary G A).card : ℝ) ≤ c*(G.cut univ A).card)
    {i : ℕ} (hi : i ∈ Dyadic.selected (fun j => (P.crossing G j).card) z) :
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ 8*c*(P.crossing G i).card := by
  classical
  let J := Dyadic.selected (fun j => (P.crossing G j).card) z
  let I := insert z J
  let K := J.filter (fun j => i ≤ j)
  let nx := fun j => nextIndex I j z
  have hn (j : ℕ) (hj : j ∈ J) : nx j ∈ I ∧ j < nx j ∧ ∀k ∈ I, j < k → nx j ≤ k :=
    nextIndex_spec (mem_insert_self _ _) (P.selected_lt_end G hz hj)
  have hcover : Bad ∩ P.crossing G i ⊆ K.biUnion (fun j => Bad ∩ (P.crossing G j \ P.crossing G (nx j))) := by
    intro e he
    obtain ⟨hBad,hei⟩ := mem_inter.mp he
    let E := J.filter (fun j => i ≤ j ∧ e ∈ P.crossing G j)
    have hei' : i ∈ E := mem_filter.mpr ⟨hi,le_rfl,hei⟩
    let j := E.max' ⟨i,hei'⟩
    have hjE : j ∈ E := max'_mem _ _
    obtain ⟨hjJ,hij,hej⟩ := mem_filter.mp hjE
    have hen : e ∉ P.crossing G (nx j) := by
      intro hen
      rcases mem_insert.mp (hn j hjJ).1 with hroot | hJ
      · rw [hroot,P.crossing_root G hz] at hen
        exact notMem_empty e hen
      · have hnx : nx j ∈ E := mem_filter.mpr ⟨hJ,hij.trans (hn j hjJ).2.1.le,hen⟩
        have hmax := le_max' E (nx j) hnx
        have hlt := (hn j hjJ).2.1
        omega
    exact mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨hjJ,hij⟩,mem_inter.mpr ⟨hBad,mem_sdiff.mpr ⟨hej,hen⟩⟩⟩
  have hcount := (card_le_card hcover).trans (card_biUnion_le)
  calc
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ ∑j ∈ K, ((Bad ∩ (P.crossing G j \ P.crossing G (nx j))).card : ℝ) := by
      exact_mod_cast hcount
    _ ≤ ∑j ∈ K, 2*c*(P.crossing G j).card := by
      apply sum_le_sum
      intro j hj
      have hjJ := (mem_filter.mp hj).1
      exact P.transition_bad_bound G hH (mem_insert_of_mem hjJ) (hn j hjJ).1
        (hn j hjJ).2.1 (hn j hjJ).2.2 Bad hc hnode
    _ = 2*c*(∑j ∈ K, ((P.crossing G j).card : ℝ)) := by rw [mul_sum]
    _ ≤ 2*c*(4*(P.crossing G i).card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Dyadic.tail_bound (fun _ _ hij => card_le_card (P.crossing_antitone G hij)) hi
    _ = _ := by ring

lemma simultaneous_bad_bound {z : ℕ} (hz : P.parts z={univ})
    {H : Hierarchy n}
    (hH : H.nodes=P.nodes (insert z (Dyadic.selected (fun j => (P.crossing G j).card) z)))
    (Bad : Finset (Fin m)) {c : ℝ} (hc : 0 ≤ c)
    (hnode : ∀A ∈ H.nodes, ((Bad ∩ H.parentBoundary G A).card : ℝ) ≤ c*(G.cut univ A).card)
    (i : ℕ) (hiz : i ≤ z) :
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ 16*c*(P.crossing G i).card := by
  classical
  by_cases hzero : (P.crossing G i).card=0
  · have hz' : P.crossing G i=∅ := card_eq_zero.mp hzero
    simp [hz']
  have hip : 0 < (P.crossing G i).card := Nat.pos_of_ne_zero hzero
  obtain ⟨j,hj,hji,hlog⟩ := Dyadic.representative (M := fun j => (P.crossing G j).card) hiz hip
  have hratio := Dyadic.same_bin_ratio hip hlog
  calc
    ((Bad ∩ P.crossing G i).card : ℝ) ≤ ((Bad ∩ P.crossing G j).card : ℝ) := by
      exact_mod_cast card_le_card (inter_subset_inter_left (P.crossing_antitone G hji))
    _ ≤ 8*c*(P.crossing G j).card := P.selected_tail_bad_bound G hz hH Bad hc hnode hj
    _ ≤ 8*c*(2*(P.crossing G i).card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hratio.le
    _ = _ := by ring

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
