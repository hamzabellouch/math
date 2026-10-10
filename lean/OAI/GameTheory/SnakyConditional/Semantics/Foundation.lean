import OAI.GameTheory.SnakyConditional.Model

namespace OAI

namespace SnakyConditional
variable {α : Type*} [DecidableEq α]
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
def inverseOrientation (r : Fin 8) : Fin 8 :=
  if r = 3 then 5 else if r = 5 then 3 else r
theorem orient_inverse_left (r : Fin 8) (p : Cell) :
    orient (inverseOrientation r) (orient r p) = p := by
  fin_cases r <;> rcases p with ⟨x, y⟩ <;> simp [orient, inverseOrientation]
theorem orient_inverse_right (r : Fin 8) (p : Cell) :
    orient r (orient (inverseOrientation r) p) = p := by
  fin_cases r <;> rcases p with ⟨x, y⟩ <;> simp [orient, inverseOrientation]
def orientationEquiv (r : Fin 8) : Cell ≃ Cell where
  toFun := orient r
  invFun := orient (inverseOrientation r)
  left_inv := orient_inverse_left r
  right_inv := orient_inverse_right r
def translationEquiv (t : Cell) : Cell ≃ Cell where
  toFun := fun p => p + t
  invFun := fun p => p - t
  left_inv := fun p => add_sub_cancel_right p t
  right_inv := fun p => sub_add_cancel p t
def placementEquiv (r : Fin 8) (t : Cell) : Cell ≃ Cell :=
  (orientationEquiv r).trans (translationEquiv t)
@[simp] theorem placementEquiv_apply (r : Fin 8) (t p : Cell) :
    placementEquiv r t p = placement r t p := rfl
@[simp] theorem coe_placementEquiv (r : Fin 8) (t : Cell) :
    (placementEquiv r t : Cell → Cell) = placement r t := rfl
def composeOrientation (r s : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6],
    ![2,5,0,7,6,1,4,3], ![3,4,1,6,7,0,5,2],
    ![4,3,6,1,0,7,2,5], ![5,2,7,0,1,6,3,4],
    ![6,7,4,5,2,3,0,1], ![7,6,5,4,3,2,1,0]] r s
theorem orient_comp (r s : Fin 8) (p : Cell) :
    orient r (orient s p) = orient (composeOrientation r s) p := by
  fin_cases r <;> fin_cases s <;> rcases p with ⟨x, y⟩ <;>
    simp [orient, composeOrientation]
theorem orient_add (r : Fin 8) (p q : Cell) :
    orient r (p + q) = orient r p + orient r q := by
  fin_cases r <;> rcases p with ⟨x, y⟩ <;> rcases q with ⟨u, v⟩ <;>
    simp [orient, add_comm]
theorem placement_comp (r s : Fin 8) (t u p : Cell) :
    placement r t (placement s u p) =
      placement (composeOrientation r s) (orient r u + t) p := by
  simp only [placement, orient_add, orient_comp, add_assoc]
theorem HasSnaky.mono {M N : Finset Cell} (h : HasSnaky M) (hMN : M ⊆ N) :
    HasSnaky N := by
  obtain ⟨r, t, hrt⟩ := h
  exact ⟨r, t, hrt.trans hMN⟩
theorem HasSnaky.placed (r : Fin 8) (t : Cell) (M : Finset Cell)
    (h : HasSnaky M) : HasSnaky (M.image (placement r t)) := by
  obtain ⟨s, u, hsu⟩ := h
  refine ⟨composeOrientation r s, orient r u + t, ?_⟩
  intro z hz
  obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
  refine Finset.mem_image.mpr ⟨placement s u p,
    hsu (Finset.mem_image_of_mem (placement s u) hp), ?_⟩
  exact (placement_comp r s t u p).trans hpz
theorem placed_template {n : ℕ} {A H : Finset Cell}
    (h : Template HasSnaky n A H) (r : Fin 8) (t : Cell) :
    Template HasSnaky n (A.image (placement r t)) (H.image (placement r t)) := by
  have hw : ∀ X, HasSnaky X → HasSnaky (X.image (placementEquiv r t)) := by
    intro X hx
    simpa only [coe_placementEquiv] using HasSnaky.placed r t X hx
  simpa only [coe_placementEquiv] using h.transport (placementEquiv r t) hw
def basePoint (i : Fin 6) : Cell := ![(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)] i
def baseEnvelope (i : Fin 6) : Finset Cell :=
  snaky.image (placement 0 (-basePoint i))
def baseRequired (i : Fin 6) : Finset Cell := (baseEnvelope i).erase (0, 0)
theorem basePoint_mem (i : Fin 6) : basePoint i ∈ snaky := by
  fin_cases i <;> decide
theorem base_works (i : Fin 6) :
    Template HasSnaky 1 (baseRequired i) (baseEnvelope i) := by
  apply immediate_template HasSnaky (baseEnvelope i) (0, 0)
  · exact Finset.mem_image.mpr ⟨basePoint i, basePoint_mem i, by simp [placement, orient]; rfl⟩
  · intro M hM
    exact ⟨0, -basePoint i, hM⟩
end SnakyConditional

end OAI
