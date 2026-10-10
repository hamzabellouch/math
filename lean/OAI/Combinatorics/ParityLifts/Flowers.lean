import OAI.Combinatorics.ParityLifts.ReducedCNF

namespace OAI

namespace Sparsification

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
lemma singletons_pairwise (A : CNF α) (hA : ∀ C ∈ A, C.card = 1) :
    (↑A : Set (Finset α)).Pairwise Disjoint := by
  intro C hC D hD hne
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (hA C hC)
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (hA D hD)
  simpa using fun he : x = y => hne (he ▸ rfl)

lemma pairwise_degree_le_one (A : CNF α) (hA : (↑A : Set (Finset α)).Pairwise Disjoint)
    (x : α) : degree A x ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro C hC D hD
  by_contra hne
  exact Finset.disjoint_left.mp
    (hA (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 hne)
    (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2

lemma singleton_degree_le_one (C : Finset α) (x : α) : degree {C} x ≤ 1 := by
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma erase_image_injective (S : CNF α) (x : α) (hx : ∀ C ∈ S, x ∈ C) :
    Set.InjOn (fun C : Finset α => C.erase x) ↑S := by
  intro C hC D hD he
  have hc := Finset.insert_erase (hx C hC)
  have hd := Finset.insert_erase (hx D hD)
  change C.erase x = D.erase x at he
  rw [← hc, ← hd, he]

lemma flower_two_of_degree {F : CNF α} {h : ℕ} (x : α)
    (hd : h ≤ degree (binaries F) x) : Nonempty (Flower F 1 1 h) := by
  obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq hd
  have hsx : ∀ C ∈ S, x ∈ C := fun C hC => (Finset.mem_filter.mp (hS hC)).2
  have hsc : ∀ C ∈ S, C.card = 2 := fun C hC =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hS hC)).1).2
  let A := S.image (fun C => C.erase x)
  have hAc : ∀ P ∈ A, P.card = 1 := by
    intro P hP
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
    rw [Finset.card_erase_of_mem (hsx C hC), hsc C hC]
  refine ⟨{
    core := {x}
    petals := A
    core_card := by simp
    petals_card := ?_
    petal_card := hAc
    apart := ?_
    pairwise := singletons_pairwise A hAc
    cover := ?_ }⟩
  · exact (Finset.card_image_of_injOn (erase_image_injective S x hsx)).trans hc
  · intro P hP
    obtain ⟨C, _hC, rfl⟩ := Finset.mem_image.mp hP
    simp
  · intro P hP
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hP
    simpa [Finset.singleton_union, Finset.insert_erase (hsx C hC)] using
      (Finset.mem_filter.mp (Finset.mem_filter.mp (hS hC)).1).1

lemma no_two_flower_degree {F : CNF α} {h : ℕ} (hn : ¬ Nonempty (Flower F 1 1 h)) :
    ∀ x, degree (binaries F) x < h := by
  intro x
  by_contra hx
  exact hn (flower_two_of_degree x (by omega))

/-- The rank-two sunflower bound, proved directly by a largest disjoint family. -/
lemma rank_two_sunflower {F : CNF α} {h : ℕ} (hsize : ∀ C ∈ F, C.card = 2)
    (hcard : 2 * h ^ 2 < F.card) :
    Nonempty (Flower F 0 2 h) ∨ Nonempty (Flower F 1 1 h) := by
  classical
  let P : Finset (CNF α) := F.powerset.filter
    (fun S : CNF α => (↑S : Set (Finset α)).Pairwise Disjoint)
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image P Finset.card
    ⟨∅, by simp [P, Set.pairwise_empty]⟩
  have hSF : S ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hpair : (↑S : Set (Finset α)).Pairwise Disjoint := (Finset.mem_filter.mp hS).2
  by_cases hh : h ≤ S.card
  · obtain ⟨A, hAS, hAc⟩ := Finset.exists_subset_card_eq hh
    left
    exact ⟨{
      core := ∅
      petals := A
      core_card := by simp
      petals_card := hAc
      petal_card := fun C hC => hsize C (hSF (hAS hC))
      apart := by intros; exact disjoint_bot_left
      pairwise := hpair.mono hAS
      cover := by intro C hC; simpa using hSF (hAS hC) }⟩
  · have cover : ∀ C ∈ F, ∃ x ∈ S.biUnion id, x ∈ C := by
      intro C hC
      by_contra hn
      have hd : ∀ D ∈ S, Disjoint C D := by
        intro D hD
        apply Finset.disjoint_left.mpr
        intro x hx hxD
        exact hn ⟨x, Finset.mem_biUnion.mpr ⟨D, hD, hxD⟩, hx⟩
      have hCS : C ∉ S := by
        intro hcs
        have hem : C = ∅ := disjoint_self.mp (hd C hcs)
        have := hsize C hC
        simp [hem] at this
      have hp : insert C S ∈ P := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hC hSF), ?_⟩
        intro D hD E hE hne
        rcases Finset.mem_insert.mp hD with hDC | hDS
        · subst D
          rcases Finset.mem_insert.mp hE with hEC | hES
          · exact False.elim (hne hEC.symm)
          · exact hd E hES
        · rcases Finset.mem_insert.mp hE with hEC | hES
          · subst E
            exact (hd D hDS).symm
          · exact hpair hDS hES hne
      have hm := hmax (insert C S) hp
      rw [Finset.card_insert_of_notMem hCS] at hm
      omega
    have hcovercard : (S.biUnion id).card ≤ 2 * S.card := by
      calc
        _ ≤ ∑ C ∈ S, C.card := Finset.card_biUnion_le
        _ = ∑ _C ∈ S, 2 := Finset.sum_congr rfl (fun C hC => hsize C (hSF hC))
        _ = _ := by simp [Nat.mul_comm]
    have hs : F ⊆ (S.biUnion id).biUnion (fun x => F.filter (fun C => x ∈ C)) := by
      intro C hC
      obtain ⟨x, hx, hxC⟩ := cover C hC
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hC, hxC⟩⟩
    have hex : ∃ x ∈ S.biUnion id, h ≤ degree F x := by
      by_contra hn
      have hdeg : ∀ x ∈ S.biUnion id, degree F x ≤ h := by
        intro x hx
        by_contra hgt
        exact hn ⟨x, hx, by omega⟩
      have hc : F.card ≤ (S.biUnion id).card * h := by
        calc
          _ ≤ ((S.biUnion id).biUnion (fun x => F.filter (fun C => x ∈ C))).card :=
            Finset.card_le_card hs
          _ ≤ ∑ x ∈ S.biUnion id, degree F x := Finset.card_biUnion_le
          _ ≤ ∑ _x ∈ S.biUnion id, h := Finset.sum_le_sum hdeg
          _ = _ := by simp
      nlinarith
    obtain ⟨x, _hx, hx⟩ := hex
    right
    apply flower_two_of_degree x
    have hb : binaries F = F := Finset.filter_eq_self.mpr hsize
    simpa [hb] using hx

end Sparsification


namespace Sparsification

variable {α : Type} [DecidableEq α]

lemma Flower.reattach {E F : CNF α} {p q h : ℕ} (f : Flower E p q h)
    (x : α) (hx : ∀ C ∈ E, x ∉ C) (hc : ∀ C ∈ E, insert x C ∈ F) (hh : 0 < h) :
    Nonempty (Flower F (p + 1) q h) := by
  have hn : x ∉ f.core := by
    obtain ⟨P, hP⟩ := Finset.card_pos.mp (by rw [f.petals_card]; exact hh)
    intro hxc
    exact hx _ (f.cover P hP) (Finset.mem_union_left _ hxc)
  refine ⟨{
    core := insert x f.core
    petals := f.petals
    core_card := by rw [Finset.card_insert_of_notMem hn, f.core_card]
    petals_card := f.petals_card
    petal_card := f.petal_card
    apart := ?_
    pairwise := f.pairwise
    cover := ?_ }⟩
  · intro P hP
    have hxp : x ∉ P := fun h => hx _ (f.cover P hP) (Finset.mem_union_right _ h)
    simp [Finset.disjoint_insert_left, hxp, f.apart P hP]
  · intro P hP
    simpa [Finset.insert_union] using hc _ (f.cover P hP)

def triples (F : CNF α) : CNF α := F.filter (fun C => C.card = 3)

lemma no_three_flower_degree {F : CNF α} {h : ℕ} (hh : 0 < h)
    (h1 : ¬ Nonempty (Flower F 1 2 h)) (h2 : ¬ Nonempty (Flower F 2 1 h)) :
    ∀ x, degree (triples F) x ≤ 2 * h ^ 2 := by
  intro x
  by_contra hgt
  let S := (triples F).filter (fun C => x ∈ C)
  have hsx : ∀ C ∈ S, x ∈ C := fun C hC => (Finset.mem_filter.mp hC).2
  have hsc : ∀ C ∈ S, C.card = 3 := fun C hC =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  let E := S.image (fun C => C.erase x)
  have hec : ∀ C ∈ E, C.card = 2 := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    rw [Finset.card_erase_of_mem (hsx D hD), hsc D hD]
  have hcard : 2 * h ^ 2 < E.card := by
    have he := Finset.card_image_of_injOn (erase_image_injective S x hsx)
    dsimp only [E]
    rw [he]
    exact Nat.lt_of_not_ge hgt
  have hex : ∀ C ∈ E, x ∉ C := by
    intro C hC
    obtain ⟨D, _hD, rfl⟩ := Finset.mem_image.mp hC
    exact Finset.notMem_erase _ _
  have heF : ∀ C ∈ E, insert x C ∈ F := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    rw [Finset.insert_erase (hsx D hD)]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hD).1).1
  rcases rank_two_sunflower hec hcard with hf | hf
  · obtain ⟨f⟩ := hf
    exact h1 (f.reattach x hex heF hh)
  · obtain ⟨f⟩ := hf
    exact h2 (f.reattach x hex heF hh)

variable [Fintype α]

lemma width_three_count (F : CNF α) (hw : ∀ C ∈ F, C.card ≤ 3) :
    F.card ≤ 1 + (units F).card + (binaries F).card + (triples F).card := by
  let U := (units F).image (fun x => ({x} : Finset α))
  have hs : F ⊆ (({∅} ∪ U) ∪ binaries F) ∪ triples F := by
    intro C hC
    have hh := hw C hC
    by_cases h2 : C.card = 2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hC, h2⟩))
    by_cases h3 : C.card = 3
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hC, h3⟩)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show C.card ≤ 1 by omega) with hz | ho
    · have hc : C = ∅ := Finset.card_eq_zero.mp hz
      subst C
      simp
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp ho
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x, (mem_units F x).mpr hC, rfl⟩
  have h0 := Finset.card_le_card hs
  have h1 := Finset.card_union_le ({∅} : CNF α) U
  have h2 := Finset.card_union_le ({∅} ∪ U) (binaries F)
  have h3 := Finset.card_union_le (({∅} ∪ U) ∪ binaries F) (triples F)
  have hU : U.card ≤ (units F).card := Finset.card_image_le
  simp only [Finset.card_singleton] at h1
  omega

lemma sparse_leaf_density (F : CNF α) (h₂ h₃ : ℕ) (hh : 0 < h₃)
    (hw : ∀ C ∈ F, C.card ≤ 3)
    (hn2 : ¬ Nonempty (Flower F 1 1 h₂))
    (hn31 : ¬ Nonempty (Flower F 1 2 h₃)) (hn32 : ¬ Nonempty (Flower F 2 1 h₃)) :
    F.card ≤ 1 + Fintype.card α * (1 + h₂ + 2 * h₃ ^ 2) := by
  have hb : (binaries F).card ≤ Fintype.card α * h₂ := by
    apply marked_card_bound
    · intro C hC
      apply Finset.card_pos.mp
      rw [(Finset.mem_filter.mp hC).2]
      omega
    · intro x
      exact (no_two_flower_degree hn2 x).le
  have ht : (triples F).card ≤ Fintype.card α * (2 * h₃ ^ 2) := by
    apply marked_card_bound
    · intro C hC
      apply Finset.card_pos.mp
      rw [(Finset.mem_filter.mp hC).2]
      omega
    · exact no_three_flower_degree hh hn31 hn32
  have hu : (units F).card ≤ Fintype.card α := Finset.card_le_univ _
  have hF := width_three_count F hw
  nlinarith

end Sparsification

end OAI
