import OAI.Combinatorics.Ramsey.CycleClique.Construction.Triangle
import Mathlib.Algebra.Group.Fin.Basic

namespace OAI

/-!
# Shortening a Hamiltonian cycle when there is no independent triple

This is Lemma `size:shortening` of the manuscript. A step-two chord
bypasses one vertex. If all such chords are absent, every step-four edge
is forced, and an explicit reordered cycle omits just vertex zero.
-/

namespace CycleClique.Construction
private theorem cycleNext_eq_add_one {r : ℕ} [NeZero r] (hr : 1 < r) (i : Fin r) :
    cycleNext i = i + 1 := by
  apply Fin.ext
  change (i.val + 1) % r = (i.val + 1 % r) % r
  rw [Nat.mod_eq_of_lt hr]

private def skipOne {r : ℕ} (hr : 3 ≤ r) (i : Fin (r - 1)) : Fin r :=
  ⟨if i.val = 0 then 0 else i.val + 1, by split_ifs <;> omega⟩

private theorem skipOne_injective {r : ℕ} (hr : 3 ≤ r) :
    Function.Injective (skipOne hr) := by
  intro i j h
  have heq := congrArg Fin.val h
  dsimp [skipOne] at heq
  apply Fin.ext
  split_ifs at heq <;> omega

private theorem adjacent_of_successive_values {r : ℕ} {G : SimpleGraph (Fin r)}
    (hc : ∀ i, G.Adj i (cycleNext i)) {u v : Fin r} (h : u.val + 1 = v.val) :
    G.Adj u v := by
  have hn : cycleNext u = v := by
    apply Fin.ext
    change (u.val + 1) % r = v.val
    rw [h, Nat.mod_eq_of_lt v.isLt]
  simpa [hn] using hc u

private theorem shorten_at_zero {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    {G : SimpleGraph (Fin r)} (hc : ∀ i, G.Adj i (cycleNext i))
    (hchord : G.Adj 0 2) : HasCycle G (r - 1) := by
  refine ⟨skipOne hr, skipOne_injective hr, ?_⟩
  intro i
  have hi := i.isLt
  by_cases hzero : i.val = 0
  · have h0 : skipOne hr i = 0 := by apply Fin.ext; simp [skipOne, hzero]
    have h2 : skipOne hr (cycleNext i) = 2 := by
      apply Fin.ext
      have hmod : (i.val + 1) % (r - 1) = 1 := by rw [hzero]; exact Nat.mod_eq_of_lt (by omega)
      simp only [skipOne, cycleNext, hmod]
      change (if 1 = 0 then 0 else 1 + 1) = 2 % r
      simp [Nat.mod_eq_of_lt (by omega : 2 < r)]
    simpa [h0, h2] using hchord
  · by_cases hlast : i.val + 1 = r - 1
    · have hnext : (cycleNext i).val = 0 := by simp [cycleNext, hlast]
      have hcycle : cycleNext (skipOne hr i) = skipOne hr (cycleNext i) := by
        apply Fin.ext
        change ((if i.val = 0 then 0 else i.val + 1) + 1) % r =
          if (cycleNext i).val = 0 then 0 else (cycleNext i).val + 1
        simp only [hzero, ↓reduceIte, hnext]
        have heq : i.val + 1 + 1 = r := by omega
        rw [heq, Nat.mod_self]
      simpa [hcycle] using hc (skipOne hr i)
    · have hnext : (cycleNext i).val = i.val + 1 :=
        Nat.mod_eq_of_lt (by omega)
      apply adjacent_of_successive_values hc
      simp only [skipOne, hzero, ↓reduceIte, hnext]
      split_ifs <;> omega

private def stepFourLabel {r : ℕ} (hr : 7 ≤ r) (i : Fin (r - 1)) : Fin r :=
  ⟨if i.val < r - 6 then i.val + 1
    else if i.val = r - 6 then r - 2
    else if i.val = r - 5 then r - 1
    else i.val - 1, by split_ifs <;> omega⟩

private theorem stepFourLabel_injective {r : ℕ} (hr : 7 ≤ r) :
    Function.Injective (stepFourLabel hr) := by
  intro i j h
  have heq := congrArg Fin.val h
  dsimp [stepFourLabel] at heq
  apply Fin.ext
  split_ifs at heq <;> omega

private theorem adjacent_of_step_four_values {r : ℕ} [NeZero r] (hr : 7 ≤ r)
    {G : SimpleGraph (Fin r)} (hfour : ∀ i, G.Adj i (i + 4))
    {u v : Fin r} (h : (u.val + 4) % r = v.val) : G.Adj u v := by
  have hfin : u + 4 = v := by
    apply Fin.ext
    change (u.val + 4 % r) % r = v.val
    rw [Nat.mod_eq_of_lt (by omega : 4 < r)]
    exact h
  simpa [hfin] using hfour u

private theorem step_four_cycle {r : ℕ} [NeZero r] (hr : 7 ≤ r)
    {G : SimpleGraph (Fin r)} (hc : ∀ i, G.Adj i (cycleNext i))
    (hfour : ∀ i, G.Adj i (i + 4)) : HasCycle G (r - 1) := by
  refine ⟨stepFourLabel hr, stepFourLabel_injective hr, ?_⟩
  intro i
  have hi := i.isLt
  by_cases hlast : i.val = r - 2
  · have hnext : (cycleNext i).val = 0 := by
      change (i.val + 1) % (r - 1) = 0
      have heq : i.val + 1 = r - 1 := by omega
      rw [heq, Nat.mod_self]
    have hu : (stepFourLabel hr i).val = r - 3 := by
      simp only [stepFourLabel, hlast]
      split_ifs <;> omega
    have hv : (stepFourLabel hr (cycleNext i)).val = 1 := by
      simp only [stepFourLabel, hnext]
      split_ifs <;> omega
    apply adjacent_of_step_four_values hr hfour
    rw [hu, hv]
    have heq : r - 3 + 4 = r + 1 := by omega
    rw [heq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : 1 < r)]
  · have hnext : (cycleNext i).val = i.val + 1 :=
      Nat.mod_eq_of_lt (by omega)
    by_cases hfirst : i.val < r - 7
    · apply adjacent_of_successive_values hc
      simp only [stepFourLabel, hnext]
      split_ifs <;> omega
    · by_cases hboundary : i.val = r - 7
      · apply adjacent_of_step_four_values hr hfour
        have hu : (stepFourLabel hr i).val = r - 6 := by
          simp only [stepFourLabel, hboundary]; split_ifs <;> omega
        have hv : (stepFourLabel hr (cycleNext i)).val = r - 2 := by
          simp only [stepFourLabel, hnext, hboundary]; split_ifs <;> omega
        rw [hu, hv]
        have heq : r - 6 + 4 = r - 2 := by omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
      · by_cases hpenultimate : i.val = r - 5
        · apply SimpleGraph.Adj.symm
          apply adjacent_of_step_four_values hr hfour
          have hu : (stepFourLabel hr i).val = r - 1 := by
            simp only [stepFourLabel, hpenultimate]; split_ifs <;> omega
          have hv : (stepFourLabel hr (cycleNext i)).val = r - 5 := by
            simp only [stepFourLabel, hnext, hpenultimate]; split_ifs <;> omega
          rw [hu, hv]
          have heq : r - 5 + 4 = r - 1 := by omega
          rw [heq, Nat.mod_eq_of_lt (by omega)]
        · apply adjacent_of_successive_values hc
          simp only [stepFourLabel, hnext]
          split_ifs <;> omega

/-- Labelled form of the manuscript's cycle-shortening lemma. -/
theorem labelled_cycle_shortening {r : ℕ} (hr : 7 ≤ r)
    {G : SimpleGraph (Fin r)} (hc : ∀ i, G.Adj i (cycleNext i))
    (hi : ¬ HasIndependent G 3) : HasCycle G (r - 1) := by
  let : NeZero r := ⟨by omega⟩
  by_cases hchord : ∃ i : Fin r, G.Adj i (i + 2)
  · obtain ⟨a, ha⟩ := hchord
    let H : SimpleGraph (Fin r) := G.comap (fun i => a + i)
    have hH : ∀ i, H.Adj i (cycleNext i) := by
      intro i
      change G.Adj (a + i) (a + cycleNext i)
      rw [cycleNext_eq_add_one (by omega), ← add_assoc,
        ← cycleNext_eq_add_one (by omega)]
      exact hc (a + i)
    have hH02 : H.Adj 0 2 := by change G.Adj (a + 0) (a + 2); simpa using ha
    exact (shorten_at_zero (by omega) hH hH02).map (fun i => a + i)
      (add_right_injective a) (fun h => h)
  · have htwo : ∀ i : Fin r, ¬ G.Adj i (i + 2) := by simpa using hchord
    have hconst : (2 : Fin r) + 2 = 4 := by
      apply Fin.ext
      change (2 % r + 2 % r) % r = 4 % r
      rw [Nat.mod_eq_of_lt (by omega : 2 < r), Nat.mod_eq_of_lt (by omega : 4 < r)]
    have hval2 : (2 : Fin r).val = 2 := by
      change 2 % r = 2
      exact Nat.mod_eq_of_lt (by omega)
    have hval4 : (4 : Fin r).val = 4 := by
      change 4 % r = 4
      exact Nat.mod_eq_of_lt (by omega)
    have h02 : (0 : Fin r) ≠ 2 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_zero, hval2] at hv
      omega
    have h04 : (0 : Fin r) ≠ 4 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_zero, hval4] at hv
      omega
    have h24 : (2 : Fin r) ≠ 4 := by
      intro h
      have hv := congrArg Fin.val h
      rw [hval2, hval4] at hv
      omega
    have hfour : ∀ i : Fin r, G.Adj i (i + 4) := by
      intro i
      by_contra hnot
      have hi2 : i ≠ i + 2 := by simpa using (add_right_injective i).ne h02
      have hi4 : i ≠ i + 4 := by simpa using (add_right_injective i).ne h04
      have hi24 : i + 2 ≠ i + 4 := (add_right_injective i).ne h24
      have hnot24 : ¬ G.Adj (i + 2) (i + 4) := by
        simpa [add_assoc, hconst] using htwo (i + 2)
      exact hi (hasIndependent_three_of_distinct_nonadjacent hi2 hi4 hi24
        (htwo i) hnot hnot24)
    exact step_four_cycle hr hc hfour

/-- A Hamiltonian cycle on at least seven vertices can be shortened by one
when the graph has no independent triple (manuscript Lemma `size:shortening`). -/
theorem cycle_shortening {V : Type*} {r : ℕ} (hr : 7 ≤ r) {G : SimpleGraph V}
    (hc : HasCycle G r) (hi : ¬ HasIndependent G 3) : HasCycle G (r - 1) := by
  obtain ⟨f, hf, he⟩ := hc
  let H : SimpleGraph (Fin r) := G.comap f
  have hH : ∀ i, H.Adj i (cycleNext i) := he
  have hI : ¬ HasIndependent H 3 := fun h => hi (h.map f hf (fun h => h))
  exact (labelled_cycle_shortening hr hH hI).map f hf (fun h => h)

/-- Repeated shortening reaches every prescribed order at least six. -/
theorem cycle_shorten_to {V : Type*} {G : SimpleGraph V} {q r : ℕ}
    (hq : 6 ≤ q) (hqr : q ≤ r) (hc : HasCycle G r)
    (hi : ¬ HasIndependent G 3) : HasCycle G q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqr
  induction d with
  | zero => simpa using hc
  | succ d ih =>
    apply ih (by omega)
    have hshort := cycle_shortening (by omega : 7 ≤ q + (d + 1)) hc hi
    simpa using hshort

end CycleClique.Construction

end OAI
