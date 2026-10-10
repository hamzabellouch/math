import OAI.Geometry.SurfaceImmersion.Correction.CorrectionScales

namespace OAI

/-! A derivative order can increase to infinity one step at a time,
waiting until any prescribed fixed-order smallness threshold holds. -/
noncomputable section
open Filter
open scoped Topology

namespace ClosedSurfaceR4.ExactCorrection

private def delayedRank (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if N (delayedRank N n) ≤ n+1 then delayedRank N n+1 else delayedRank N n

private lemma delayedRank_step (N : ℕ → ℕ) (n : ℕ) :
    delayedRank N n ≤ delayedRank N (n+1) ∧
      delayedRank N (n+1) ≤ delayedRank N n+1 := by
  rw [delayedRank]
  split_ifs <;> omega

private lemma delayedRank_monotone (N : ℕ → ℕ) : Monotone (delayedRank N) :=
  monotone_nat_of_le_succ (fun n => (delayedRank_step N n).1)

private lemma delayedRank_threshold (N : ℕ → ℕ) (n : ℕ) :
    0 < delayedRank N n → N (delayedRank N n-1) ≤ n := by
  induction n with
  | zero => simp [delayedRank]
  | succ n ih =>
      rw [delayedRank]
      split_ifs with h
      · intro _
        simpa only [Nat.add_sub_cancel] using h
      · intro hpos
        exact (ih hpos).trans (Nat.le_succ n)

private lemma delayedRank_cofinal (N : ℕ → ℕ) (m : ℕ) :
    ∃ n, m ≤ delayedRank N n := by
  induction m with
  | zero => exact ⟨0,Nat.zero_le _⟩
  | succ m ih =>
      obtain ⟨n,hn⟩ := ih
      let p := max n (N m)
      have hp : m ≤ delayedRank N p := hn.trans (delayedRank_monotone N (le_max_left _ _))
      by_cases hlarge : m < delayedRank N p
      · exact ⟨p,hlarge⟩
      · have he : delayedRank N p = m := by omega
        have hNp : N (delayedRank N p) ≤ p+1 := by
          rw [he]
          exact (le_max_right n (N m)).trans (Nat.le_succ p)
        refine ⟨p+1,?_⟩
        rw [delayedRank,ite_eq_left hNp,he]

/-- No rate of convergence is required: each finite-order threshold
can be reached before increasing the order, with increments at most one. -/
theorem exists_slow_order_schedule {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0))
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) :
    ∃ k : ℕ → ℕ, k 0 = 0 ∧ Tendsto k atTop atTop ∧
      (∀ n, k n ≤ k (n+1) ∧ k (n+1) ≤ k n+1) ∧
      ∀ n, 0 < k n → t n < ε (k n-1) := by
  classical
  have hN : ∀ j, ∃ N : ℕ, ∀ n ≥ N, t n < ε j := by
    intro j
    exact eventually_atTop.mp (ht.eventually (gt_mem_nhds (hε j)))
  choose N hN using hN
  refine ⟨delayedRank N,rfl,?_,delayedRank_step N,?_⟩
  · exact (delayedRank_monotone N).tendsto_atTop_atTop_iff.mpr (delayedRank_cofinal N)
  · intro n hn
    exact hN (delayedRank N n-1) n (delayedRank_threshold N n hn)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
