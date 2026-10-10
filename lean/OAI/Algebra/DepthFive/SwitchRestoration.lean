import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335.SwitchRestoration

variable {ι : Type*} [DecidableEq ι]

/-- Switches in a Boolean labeling along a finite collection of oriented edges. -/
def switchCount (edges : Finset (ι × ι)) (w : ι → Bool) : ℕ :=
  ∑ e ∈ edges, if w e.1 ≠ w e.2 then 1 else 0

/-- The number of edge endpoints at a vertex, counting both ends of a loop. -/
def endpointDegree (edges : Finset (ι × ι)) (i : ι) : ℕ :=
  ∑ e ∈ edges, ((if e.1 = i then 1 else 0) + (if e.2 = i then 1 else 0))

private theorem edge_switch_restore (S : Finset ι) (y : ι → Bool) (a b : ι)
    (hnear : a ∈ S ∨ b ∈ S → y a = true ∧ y b = true)
    (hind : ¬ (a ∈ S ∧ b ∈ S)) :
    (if (if a ∈ S then false else y a) ≠ (if b ∈ S then false else y b) then 1 else 0) =
      (if y a ≠ y b then 1 else 0) +
        (if a ∈ S then 1 else 0) + (if b ∈ S then 1 else 0) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · exact False.elim (hind ⟨ha, hb⟩)
  · obtain ⟨hya, hyb⟩ := hnear (Or.inl ha)
    simp [ha, hb, hya, hyb]
  · obtain ⟨hya, hyb⟩ := hnear (Or.inr hb)
    simp [ha, hb, hya, hyb]
  · simp [ha, hb]

/-- Restoring an independent subset of all-true neighborhoods creates one switch per incident edge. -/
theorem switchCount_restore_eq (edges : Finset (ι × ι)) (S : Finset ι) (y : ι → Bool)
    (hnear : ∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S → y e.1 = true ∧ y e.2 = true)
    (hind : ∀ e ∈ edges, ¬ (e.1 ∈ S ∧ e.2 ∈ S)) :
    switchCount edges (fun i => if i ∈ S then false else y i) =
      switchCount edges y + ∑ i ∈ S, endpointDegree edges i := by
  unfold switchCount endpointDegree
  rw [Finset.sum_comm (s := S) (t := edges)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_add_distrib]
  have ha : (∑ i ∈ S, if e.1 = i then 1 else 0) = if e.1 ∈ S then 1 else 0 := by
    simp [eq_comm]
  have hb : (∑ i ∈ S, if e.2 = i then 1 else 0) = if e.2 ∈ S then 1 else 0 := by
    simp [eq_comm]
  rw [ha, hb]
  simpa [Nat.add_assoc] using edge_switch_restore S y e.1 e.2 (hnear e he) (hind e he)

/-- Every restored interior vertex of a path creates exactly two switches. -/
theorem switchCount_restore_eq_add_twice_card
    (edges : Finset (ι × ι)) (S : Finset ι) (y : ι → Bool)
    (hnear : ∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S → y e.1 = true ∧ y e.2 = true)
    (hind : ∀ e ∈ edges, ¬ (e.1 ∈ S ∧ e.2 ∈ S))
    (hdegree : ∀ i ∈ S, endpointDegree edges i = 2) :
    switchCount edges (fun i => if i ∈ S then false else y i) =
      switchCount edges y + 2 * S.card := by
  rw [switchCount_restore_eq edges S y hnear hind]
  congr 1
  calc
    ∑ i ∈ S, endpointDegree edges i = ∑ _i ∈ S, 2 :=
      Finset.sum_congr rfl hdegree
    _ = 2 * S.card := by simp [Nat.mul_comm]


/-- Edges of the path with `n+1` vertices. -/
def pathEdges (n : ℕ) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  Finset.univ.image fun i : Fin n => (i.castSucc, i.succ)

theorem path_edge_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => (i.castSucc, i.succ)) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun e : Fin (n + 1) × Fin (n + 1) => e.1.val) h

/-- This switch count agrees with the usual adjacent-position sum. -/
theorem switchCount_pathEdges (n : ℕ) (w : Fin (n + 1) → Bool) :
    switchCount (pathEdges n) w =
      ∑ i : Fin n, if w i.castSucc ≠ w i.succ then 1 else 0 := by
  unfold switchCount pathEdges
  rw [Finset.sum_image]
  exact fun i hi j hj h => path_edge_injective n h

theorem endpointDegree_pathEdges_interior {n : ℕ} (i : Fin (n + 1))
    (hleft : 0 < i.val) (hright : i.val < n) :
    endpointDegree (pathEdges n) i = 2 := by
  unfold endpointDegree pathEdges
  rw [Finset.sum_image]
  · rw [Finset.sum_add_distrib]
    have hr : (∑ j : Fin n, if j.castSucc = i then 1 else 0) = 1 := by
      let r : Fin n := ⟨i.val, hright⟩
      have hri : r.castSucc = i := by apply Fin.ext; rfl
      rw [Finset.sum_eq_single r]
      · simp [hri]
      · intro j hj hne
        have hji : j.castSucc ≠ i := by
          intro h
          apply hne
          apply Fin.ext
          simpa [r] using congrArg (fun x : Fin (n + 1) => x.val) h
        simp [hji]
      · simp
    have hl : (∑ j : Fin n, if j.succ = i then 1 else 0) = 1 := by
      let l : Fin n := ⟨i.val - 1, by omega⟩
      have hli : l.succ = i := by apply Fin.ext; simp only [Fin.val_succ]; dsimp [l]; omega
      rw [Finset.sum_eq_single l]
      · simp [hli]
      · intro j hj hne
        have hji : j.succ ≠ i := by
          intro h
          apply hne
          apply Fin.ext
          have := congrArg Fin.val h
          dsimp [l]
          simp only [Fin.val_succ] at this
          omega
        simp [hji]
      · simp
    change (∑ j : Fin n, if j.castSucc = i then 1 else 0) +
      (∑ j : Fin n, if j.succ = i then 1 else 0) = 2
    rw [hr, hl]
  · exact fun a ha b hb h => path_edge_injective n h


/-- The path specialization states all hypotheses directly on neighboring indices. -/
theorem path_switchCount_restore_eq {n : ℕ} (S : Finset (Fin (n + 1)))
    (y : Fin (n + 1) → Bool)
    (hinterior : ∀ i ∈ S, 0 < i.val ∧ i.val < n)
    (hnear : ∀ j : Fin n, j.castSucc ∈ S ∨ j.succ ∈ S →
      y j.castSucc = true ∧ y j.succ = true)
    (hind : ∀ j : Fin n, ¬ (j.castSucc ∈ S ∧ j.succ ∈ S)) :
    switchCount (pathEdges n) (fun i => if i ∈ S then false else y i) =
      switchCount (pathEdges n) y + 2 * S.card := by
  apply switchCount_restore_eq_add_twice_card
  · intro e he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact hnear j
  · intro e he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
    exact hind j
  · intro i hi
    exact endpointDegree_pathEdges_interior i (hinterior i hi).1 (hinterior i hi).2

/-- Restoring false symbols removes exactly the chosen true symbols. -/
theorem trueVertices_restore_eq_sdiff (V S : Finset ι) (y : ι → Bool) :
    (V.filter fun i => (if i ∈ S then false else y i) = true) =
      (V.filter fun i => y i = true) \ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi, and_comm]

/-- Cardinal form without truncated subtraction, suitable for exponent arithmetic. -/
theorem trueVertices_restore_card_add (V S : Finset ι) (y : ι → Bool)
    (hS : S ⊆ V) (hy : ∀ i ∈ S, y i = true) :
    (V.filter fun i => (if i ∈ S then false else y i) = true).card + S.card =
      (V.filter fun i => y i = true).card := by
  rw [trueVertices_restore_eq_sdiff]
  apply Finset.card_sdiff_add_card_eq_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨hS hi, hy i hi⟩

end Problem335.SwitchRestoration

end

end OAI
