import OAI.Analysis.IrrationalRotation.Analysis.FrequencySplice

namespace OAI

namespace Invariant233.PrescribedPhaseRealization

theorem frequencyTower_stable (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d)
    (hkeep : ∀ j i, i ≤ d j → q (j + 1) i = q j i)
    {j k i : ℕ} (hjk : j ≤ k) (hi : i ≤ d j) : q k i = q j i := by
  induction k with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      rfl
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst j
        rfl
      · have hjk' : j ≤ k := by omega
        calc
          q (k + 1) i = q k i := hkeep k i (hi.trans (hd hjk'))
          _ = q j i := ih hjk'

theorem exists_frequency_of_prefix_tower (d : ℕ → ℕ) (q : ℕ → ℕ → ℕ)
    (hd : Monotone d) (hcover : ∀ j, j ≤ d j)
    (hkeep : ∀ j i, i ≤ d j → q (j + 1) i = q j i)
    (hpos : ∀ j i, i ≤ d j → 0 < q j i)
    (hmono : ∀ j i, i < d j → q j i < q j (i + 1))
    (hdiv : ∀ j i, i < d j → q j i ∣ q j (i + 1)) :
    ∃ Q : ℕ → ℕ, (∀ j i, i ≤ d j → Q i = q j i) ∧
      (∀ i, 0 < Q i) ∧ StrictMono Q ∧ (∀ i, Q i ∣ Q (i + 1)) := by
  let Q : ℕ → ℕ := fun i => q i i
  have hagree : ∀ j i, i ≤ d j → Q i = q j i := by
    intro j i hi
    have ha := frequencyTower_stable d q hd hkeep (le_max_right j i) (hcover i)
    have hb := frequencyTower_stable d q hd hkeep (le_max_left j i) hi
    exact ha.symm.trans hb
  refine ⟨Q, hagree, ?_, ?_, ?_⟩
  · intro i
    exact hpos i i (hcover i)
  · apply strictMono_nat_of_lt_succ
    intro i
    have hi : i < d (i + 1) := (Nat.lt_succ_self i).trans_le (hcover (i + 1))
    rw [hagree (i + 1) i hi.le, hagree (i + 1) (i + 1) (hcover (i + 1))]
    exact hmono (i + 1) i hi
  · intro i
    have hi : i < d (i + 1) := (Nat.lt_succ_self i).trans_le (hcover (i + 1))
    rw [hagree (i + 1) i hi.le, hagree (i + 1) (i + 1) (hcover (i + 1))]
    exact hdiv (i + 1) i hi

theorem prefix_test_eq {ι α : Type*} (Q q : ℕ → ℕ) (p : ℕ)
    (hkeep : ∀ i ≤ p, Q i = q i) (indices : ι → ℕ)
    (hindices : ∀ i, indices i ≤ p) (test : (ι → ℕ) → α) :
    test (fun i => Q (indices i)) = test (fun i => q (indices i)) := by
  congr 1
  funext i
  exact hkeep (indices i) (hindices i)

end Invariant233.PrescribedPhaseRealization

end OAI
