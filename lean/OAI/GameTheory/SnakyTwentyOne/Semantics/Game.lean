import OAI.GameTheory.SnakyTwentyOne.Model

namespace OAI

namespace SnakyPrototype
variable {α : Type*} [DecidableEq α]
inductive WinsIn (win : Finset α → Prop) : ℕ → Finset α → Finset α → Prop
  | done {n M B} : win M → WinsIn win n M B
  | move {n M B} (x : α) (hxM : x ∉ M) (hxB : x ∉ B)
      (next : ∀ b, b ∉ insert x M → b ∉ B →
        WinsIn win n (insert x M) (insert b B)) :
      WinsIn win (n + 1) M B
theorem WinsIn.weaken {win : Finset α → Prop} {n : ℕ} {M B : Finset α}
    (h : WinsIn win n M B) : ∀ k, WinsIn win (n + k) M B := by
  induction h with
  | done hw =>
      intro k
      exact WinsIn.done hw
  | @move n M B x hxM hxB next ih =>
      intro k
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (WinsIn.move x hxM hxB (fun b hbM hbB => ih b hbM hbB k))
theorem WinsIn.mono {win : Finset α → Prop} {n m : ℕ} {M B : Finset α}
    (h : WinsIn win n M B) (hnm : n ≤ m) : WinsIn win m M B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact h.weaken k
def Template (win : Finset α → Prop) (n : ℕ) (A H : Finset α) : Prop :=
  ∀ M B, Disjoint M B → A ⊆ M → Disjoint B H → WinsIn win n M B
theorem WinsIn.transport {win : Finset α → Prop} {n : ℕ} {M B : Finset α}
    (h : WinsIn win n M B) (e : α ≃ α)
    (hwin : ∀ X, win X → win (X.image e)) :
    WinsIn win n (M.image e) (B.image e) := by
  induction h with
  | done hw => exact WinsIn.done (hwin _ hw)
  | @move n M B x hxM hxB next ih =>
      apply WinsIn.move (e x)
      · intro hx
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
        exact hxM (e.injective he ▸ hy)
      · intro hx
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
        exact hxB (e.injective he ▸ hy)
      · intro b hbM hbB
        have hbM' : e.symm b ∉ insert x M := by
          intro hb
          apply hbM
          simpa [Finset.image_insert] using Finset.mem_image_of_mem e hb
        have hbB' : e.symm b ∉ B := by
          intro hb
          apply hbB
          simpa using Finset.mem_image_of_mem e hb
        simpa [Finset.image_insert] using ih (e.symm b) hbM' hbB'
theorem Template.mono {win : Finset α → Prop} {n m : ℕ} {A H : Finset α}
    (h : Template win n A H) (hnm : n ≤ m) : Template win m A H := by
  intro M B hMB hAM hBH
  exact (h M B hMB hAM hBH).mono hnm
theorem Template.transport {win : Finset α → Prop} {n : ℕ} {A H : Finset α}
    (h : Template win n A H) (e : α ≃ α)
    (hwin : ∀ X, win X → win (X.image e)) :
    Template win n (A.image e) (H.image e) := by
  intro M B hMB hAM hBH
  have hMB' : Disjoint (M.image e.symm) (B.image e.symm) := by
    refine Finset.disjoint_left.mpr ?_
    intro z hzM hzB
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hzM
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hzB
    have hxy : x = y := e.symm.injective (hxe.trans hye.symm)
    exact Finset.disjoint_left.mp hMB hx (hxy.symm ▸ hy)
  have hAM' : A ⊆ M.image e.symm := by
    intro z hz
    exact Finset.mem_image.mpr ⟨e z, hAM (Finset.mem_image_of_mem e hz), by simp⟩
  have hBH' : Disjoint (B.image e.symm) H := by
    refine Finset.disjoint_left.mpr ?_
    intro z hzB hzH
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hzB
    have hxH : x ∈ H.image e := by
      exact Finset.mem_image.mpr ⟨z, hzH, by rw [← he]; simp⟩
    exact Finset.disjoint_left.mp hBH hx hxH
  have h' := (h (M.image e.symm) (B.image e.symm) hMB' hAM' hBH').transport e hwin
  simpa [Finset.image_image, Function.comp_def] using h'
theorem immediate_template (win : Finset α → Prop) (H : Finset α) (pivot : α)
    (hp : pivot ∈ H) (hwin : ∀ M, H ⊆ M → win M) :
    Template win 1 (H.erase pivot) H := by
  intro M B _ hAM hBH
  have hsub : H ⊆ insert pivot M := by
    intro y hy
    by_cases hyp : y = pivot
    · simp [hyp]
    · exact Finset.mem_insert_of_mem (hAM (Finset.mem_erase.mpr ⟨hyp, hy⟩))
  by_cases hpM : pivot ∈ M
  · exact WinsIn.done (hwin M (by simpa [Finset.insert_eq_of_mem hpM] using hsub))
  · apply WinsIn.move pivot hpM
    · exact fun hpB => Finset.disjoint_left.mp hBH hpB hp
    · intro b _ _
      exact WinsIn.done (hwin (insert pivot M) hsub)
theorem surviving_child {ι : Type*} [Nonempty ι]
    (C D : ι → Finset α) (M B H : Finset α)
    (hC : ∀ j, C j ⊆ M) (hD : ∀ j, D j ⊆ H)
    (hcommon : ∀ b, (∀ j, b ∈ D j) → b ∈ M)
    (hBH : Disjoint B H) (b : α) (hbM : b ∉ M) :
    ∃ j, C j ⊆ M ∧ Disjoint (insert b B) (D j) := by
  classical
  have hex : ∃ j, b ∉ D j := by
    by_contra h
    push Not at h
    exact hbM (hcommon b h)
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hC j, Finset.disjoint_left.mpr ?_⟩
  intro x hx hxd
  rcases Finset.mem_insert.mp hx with hxb | hxB
  · subst x
    exact hj hxd
  · exact Finset.disjoint_left.mp hBH hxB (hD j hxd)
theorem legal_pivot_or_replacement [Infinite α]
    (pivot : α) (M B : Finset α) (hpB : pivot ∉ B) :
    ∃ x, x ∉ M ∧ x ∉ B ∧ pivot ∈ insert x M := by
  classical
  by_cases hpM : pivot ∈ M
  · obtain ⟨x, hx⟩ := (M ∪ B).exists_notMem
    refine ⟨x, ?_, ?_, Finset.mem_insert_of_mem hpM⟩
    · exact fun hxM => hx (Finset.mem_union_left B hxM)
    · exact fun hxB => hx (Finset.mem_union_right M hxB)
  · exact ⟨pivot, hpM, hpB, Finset.mem_insert_self pivot M⟩
theorem breaker_turn {ι : Type*} [Nonempty ι]
    (win : Finset α → Prop) (n : ℕ) (C D : ι → Finset α)
    (hchild : ∀ j, Template win n (C j) (D j))
    (M B H : Finset α) (hMB : Disjoint M B)
    (hC : ∀ j, C j ⊆ M) (hD : ∀ j, D j ⊆ H)
    (hcommon : ∀ b, (∀ j, b ∈ D j) → b ∈ M)
    (hBH : Disjoint B H) :
    ∀ b, b ∉ M → b ∉ B → WinsIn win n M (insert b B) := by
  intro b hbM _
  obtain ⟨j, hjC, hjD⟩ := surviving_child C D M B H hC hD hcommon hBH b hbM
  apply hchild j M (insert b B) _ hjC hjD
  refine Finset.disjoint_left.mpr ?_
  intro x hxM hxB
  rcases Finset.mem_insert.mp hxB with hxb | hxB
  · subst x
    exact hbM hxM
  · exact Finset.disjoint_left.mp hMB hxM hxB
theorem compose [Infinite α] {ι : Type*} [Nonempty ι]
    (win : Finset α → Prop) (n : ℕ) (C D : ι → Finset α)
    (hchild : ∀ j, Template win n (C j) (D j))
    (pivot : α) (A H : Finset α) (hpH : pivot ∈ H)
    (hC : ∀ j, C j ⊆ insert pivot A)
    (hD : ∀ j, D j ⊆ H)
    (hcommon : ∀ b, (∀ j, b ∈ D j) → b ∈ insert pivot A) :
    Template win (n + 1) A H := by
  intro M B hMB hAM hBH
  have hpB : pivot ∉ B := fun hp => Finset.disjoint_left.mp hBH hp hpH
  obtain ⟨x, hxM, hxB, hpx⟩ := legal_pivot_or_replacement pivot M B hpB
  have howned : insert pivot A ⊆ insert x M := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hyp | hyA
    · subst y
      exact hpx
    · exact Finset.mem_insert_of_mem (hAM hyA)
  have hMB' : Disjoint (insert x M) B := by
    refine Finset.disjoint_left.mpr ?_
    intro y hy hyB
    rcases Finset.mem_insert.mp hy with hyx | hyM
    · subst y
      exact hxB hyB
    · exact Finset.disjoint_left.mp hMB hyM hyB
  apply WinsIn.move x hxM hxB
  exact breaker_turn win n C D hchild (insert x M) B H hMB'
    (fun j => (hC j).trans howned) hD
    (fun b hb => howned (hcommon b hb)) hBH
theorem one_stone_after_distant_reply {ι : Type*} [Nonempty ι]
    (win : Finset α → Prop) (n : ℕ) (o : α) (N : Finset α)
    (D : ι → Finset α)
    (hchild : ∀ j, Template win n {o} (D j))
    (hcommon : ∀ q, (∀ j, q ∈ D j) → q ∈ N)
    (q : α) (hqo : q ≠ o) (hqN : q ∉ N) :
    WinsIn win n {o} {q} := by
  classical
  have hex : ∃ j, q ∉ D j := by
    by_contra h
    push Not at h
    exact hqN (hcommon q h)
  obtain ⟨j, hj⟩ := hex
  apply hchild j {o} {q}
  · simpa [Finset.disjoint_singleton_left, eq_comm] using hqo
  · exact Finset.Subset.refl _
  · exact Finset.disjoint_singleton_left.mpr hj
theorem from_first_reply (win : Finset α → Prop) (n : ℕ) (o : α)
    (h : ∀ q, q ≠ o → WinsIn win n {o} {q}) :
    WinsIn win (n + 1) ∅ ∅ := by
  apply WinsIn.move o (by simp) (by simp)
  intro q hq _
  simpa using h q (by simpa using hq)
end SnakyPrototype

end OAI
