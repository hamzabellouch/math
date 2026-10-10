import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace InvariantProjection.IndependentAngles

theorem consecutiveBlocks_bijective (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    Function.Bijective
      (fun i : Σ j, Fin (m j) => (∑ r ∈ Finset.range i.1, m r) + i.2.val) := by
  let d : ℕ → ℕ := fun j => ∑ r ∈ Finset.range j, m r
  have hd0 : d 0 = 0 := by simp [d]
  have hstep : ∀ j, d (j + 1) = d j + m j := fun j => Finset.sum_range_succ m j
  have hmono : Monotone d := fun j k hjk =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hjk)
  have hlarge : ∀ j, j ≤ d j := by
    intro j
    induction j with
    | zero => omega
    | succ j hj =>
        have hp := hm j
        rw [hstep]
        omega
  have hgap : ∀ {j k}, j < k → d j + m j ≤ d k := by
    intro j k hjk
    rw [← hstep]
    exact hmono (by omega)
  constructor
  · rintro ⟨j, u⟩ ⟨k, v⟩ heq
    change d j + u.val = d k + v.val at heq
    have hjk : j = k := by
      rcases lt_trichotomy j k with h | h | h
      · have hg := hgap h
        have hu := u.isLt
        omega
      · exact h
      · have hg := hgap h
        have hv := v.isLt
        omega
    subst k
    have huv : u = v := Fin.ext (by omega)
    subst v
    rfl
  · intro n
    have hex : ∃ j, n < d (j + 1) := ⟨n, by have := hlarge (n + 1); omega⟩
    let j := Nat.find hex
    have hupper : n < d (j + 1) := Nat.find_spec hex
    have hlower : d j ≤ n := by
      by_cases hj : j = 0
      · simp [hj, hd0]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hn : ¬n < d (j - 1 + 1) := Nat.find_min hex (by change j - 1 < j; omega)
        have hpred : j - 1 + 1 = j := by omega
        rw [hpred] at hn
        omega
    have hi : n - d j < m j := by
      rw [hstep] at hupper
      omega
    refine ⟨⟨j, ⟨n - d j, hi⟩⟩, ?_⟩
    change d j + (n - d j) = n
    omega

theorem exists_consecutiveBlocks_equiv (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    ∃ e : ℕ ≃ Σ j, Fin (m j), ∀ i : Σ j, Fin (m j),
      e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val := by
  let e : (Σ j, Fin (m j)) ≃ ℕ :=
    Equiv.ofBijective _ (consecutiveBlocks_bijective m hm)
  exact ⟨e.symm, fun _ => rfl⟩

end InvariantProjection.IndependentAngles

end OAI
