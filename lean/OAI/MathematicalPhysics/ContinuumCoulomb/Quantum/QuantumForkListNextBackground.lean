import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListNextValid

namespace OAI

/-! Bounded, loop-free ordinary bonds survive the actual list transformation.
Together with port separation this supplies every hypothesis of the next
full-space fork comparison. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem unpairedBonds_valid {n : ℕ} {gs : Groups} (h : ValidPorts n gs)
    (b : Bond) (hb : b ∈ unpairedBonds gs) : b.1 < n ∧ b.2.1 < n ∧ b.1 ≠ b.2.1 := by
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' := List.mem_range.mp hi
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  have hp' : p ∈ groupAt gs i := List.mem_of_mem_drop hp
  obtain ⟨j,hj,hp⟩ := List.getElem_of_mem hp'
  have he : portAt (groupAt gs i) j=p := (portAt_eq_getElem _ _ hj).trans hp
  have hbound := h.bounded ⟨i,hi'⟩ ⟨j,hj⟩
  have hne := h.disjoint ⟨i,hi'⟩ ⟨i,hi'⟩ ⟨j,hj⟩
  rw [he] at hbound hne
  exact ⟨lt_of_lt_of_le hi' h.centers,hbound,hne⟩

theorem pairBonds_valid (n r i a b : ℕ) (R J K : ℚ)
    (hi : i < r) (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (e : Bond) (he : e ∈ pairBonds n i R ((a,J),(b,K))) :
    e.1 < n+2*r ∧ e.2.1 < n+2*r ∧ e.1 ≠ e.2.1 := by
  simp only [pairBonds,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem addedBonds_valid (s : State) (h : ValidPorts s.1 s.2.2.2) (R : ℚ)
    (b : Bond) (hb : b ∈ addedBonds s R) :
    b.1 < s.1+2*pairCount s.2.2.2 ∧ b.2.1 < s.1+2*pairCount s.2.2.2 ∧
      b.1 ≠ b.2.1 := by
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  have hi' : i < pairCount s.2.2.2 := by
    simpa only [catalog_length] using List.mem_range.mp hi
  rw [catalog_actualSite h ⟨i,hi'⟩] at hb
  have hne : actualSite h ⟨i,hi'⟩ 1 ≠ actualSite h ⟨i,hi'⟩ 2 := by
    intro he
    have := actualSite_injective h ⟨i,hi'⟩ he
    norm_num at this
  exact pairBonds_valid s.1 (pairCount s.2.2.2) i _ _ R _ _ hi'
    (actualSite h ⟨i,hi'⟩ 1).isLt (actualSite h ⟨i,hi'⟩ 2).isLt
    (fun he => hne (Fin.ext he)) b hb

theorem next_background_valid (s : State) (h : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    SourceBondLists.bounded (next N s).1 (background (next N s)) ∧
      ∀ b ∈ background (next N s), b.1 ≠ b.2.1 := by
  have hv : ∀ b ∈ background (next N s),
      b.1 < (next N s).1 ∧ b.2.1 < (next N s).1 ∧ b.1 ≠ b.2.1 := by
    intro b hmem
    change b ∈ (s.2.1++addedBonds s (scale N s))++unpairedBonds (next N s).2.2.2 at hmem
    rcases List.mem_append.mp hmem with hold | hport
    · rcases List.mem_append.mp hold with hold | hnew
      · have hm : b ∈ background s := List.mem_append_left _ hold
        have hbb := hb b hm
        have hnn := hn b hm
        rw [next_count]
        exact ⟨lt_of_lt_of_le hbb.1 (Nat.le_add_right _ _),
          lt_of_lt_of_le hbb.2 (Nat.le_add_right _ _),hnn⟩
      · exact addedBonds_valid s h (scale N s) b hnew
    · exact unpairedBonds_valid (next_validPorts N s h) b hport
  exact ⟨fun b hm => ⟨(hv b hm).1,(hv b hm).2.1⟩,fun b hm => (hv b hm).2.2⟩

theorem iterate_background_valid (s : State) (h : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (k : ℕ) :
    SourceBondLists.bounded (iterate N k s).1 (background (iterate N k s)) ∧
      ∀ b ∈ background (iterate N k s), b.1 ≠ b.2.1 := by
  induction k with
  | zero => exact ⟨hb,hn⟩
  | succ k ih =>
    exact next_background_valid _ (iterate_validPorts N s h k) ih.1 ih.2 N

end ContinuumCoulomb.QuantumForkList

end

end OAI
