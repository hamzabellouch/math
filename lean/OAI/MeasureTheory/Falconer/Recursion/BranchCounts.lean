import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions

namespace OAI

namespace PlanarFalconer

def branchCount (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) : ℕ :=
  ∑ j ∈ Finset.range n, if label j = kind then 1 else 0

theorem branchCount_card (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label n kind = ((Finset.range n).filter fun j => label j = kind).card := by
  simp [branchCount]

theorem branchCount_succ (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label (n+1) kind = branchCount label n kind + if label n = kind then 1 else 0 := by
  simp only [branchCount,Finset.sum_range_succ]

structure PolicyBranch (A : ℕ → ℝ) (N q : ℕ) (sig : ℝ) (n : ℕ) where
  state : ℕ → BranchState
  label : ℕ → BranchLabel
  valid : ∀ j ≤ n, (state j).Valid N sig
  step : ∀ j < n, BranchStep A N q sig (state j) (label j) (state (j+1))

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

def initialSegment (b : PolicyBranch A N q sig n) (m : ℕ) (hm : m ≤ n) : PolicyBranch A N q sig m :=
  ⟨b.state,b.label,fun j hj => b.valid j (hj.trans hm),fun j hj => b.step j (hj.trans_le hm)⟩

theorem nested (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    MonotoneOn (fun j => (b.state j).start) (Set.Icc 0 n) ∧
    AntitoneOn (fun j => (b.state j).finish) (Set.Icc 0 n) := by
  have hpair : ∀ j k, j ≤ k → k ≤ n →
      (b.state j).start ≤ (b.state k).start ∧ (b.state k).finish ≤ (b.state j).finish := by
    intro j k hjk hkn
    induction k, hjk using Nat.le_induction with
    | base => exact ⟨le_rfl,le_rfl⟩
    | succ k hjk ih =>
      have hp := ih (by omega)
      have hs := (b.step k (by omega)).nested hq (b.valid k (by omega))
      exact ⟨hp.1.trans hs.1,hs.2.trans hp.2⟩
  exact ⟨fun _ _ _ hk hjk => (hpair _ _ hjk hk.2).1,
    fun _ _ _ hk hjk => (hpair _ _ hjk hk.2).2⟩

noncomputable def chargedNear (b : PolicyBranch A N q sig n) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun j => b.label j = .near ∧ ChargedNear A N q (b.state j) (b.state (j+1))

noncomputable def charges (b : PolicyBranch A N q sig n) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun j => b.label j = .high ∨ b.label j = .direct ∨
    b.label j = .near ∧ ChargedNear A N q (b.state j) (b.state (j+1))

theorem charges_card (b : PolicyBranch A N q sig n) :
    b.charges.card = branchCount b.label n .high + branchCount b.label n .direct + b.chargedNear.card := by
  classical
  simp only [charges,chargedNear,Finset.card_filter,branchCount,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases b.label j <;> simp

theorem charges_have_representatives (b : PolicyBranch A N q sig n) (hq : 0 < q)
    {j : ℕ} (hj : j ∈ b.charges) :
    ∃ p ∈ policyRepresentatives A N q, (b.state j).start < p ∧ p ≤ (b.state (j+1)).start := by
  classical
  obtain ⟨hj,hlabel⟩ := Finset.mem_filter.mp hj
  have hjn := Finset.mem_range.mp hj
  rcases hlabel with hh | hd | ⟨hn,he⟩
  · have hg := (b.step j hjn).graph_charge hq (b.valid j hjn.le) (Or.inl hh)
    exact ⟨_,hg.2,hg.1,le_rfl⟩
  · have hg := (b.step j hjn).graph_charge hq (b.valid j hjn.le) (Or.inr hd)
    exact ⟨_,hg.2,hg.1,le_rfl⟩
  · obtain ⟨_,e,he,_,ha,hp⟩ := he
    have hr : descriptorAnchor e ∈ policyRepresentatives A N q := by
      cases hs : b.state j <;> rw [hs] at he
      · exact policyDescriptor_anchor_mem A hq he
      · exact policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp he).1
    exact ⟨descriptorAnchor e,hr,ha,hp⟩

theorem representative_counts (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    branchCount b.label n .high + branchCount b.label n .direct + b.chargedNear.card ≤
        (policyRepresentatives A N q).card ∧
      (policyRepresentatives A N q).card ≤ N/q+1 := by
  classical
  let charge := fun j => if hj : j ∈ b.charges then
    Classical.choose (b.charges_have_representatives hq hj) else 0
  have hspec (j : ℕ) (hj : j ∈ b.charges) :
      charge j ∈ policyRepresentatives A N q ∧
      (b.state j).start < charge j ∧ charge j ≤ (b.state (j+1)).start := by
    simpa only [charge,dite_eq_left hj] using Classical.choose_spec (b.charges_have_representatives hq hj)
  have hb := branch_representative_charges_bound A N q n (fun j => (b.state j).start)
    charge b.charges (Finset.filter_subset _ _) (b.nested hq).1
    (fun j hj => (hspec j hj).2) (fun j hj => (hspec j hj).1)
  exact ⟨by rw [← b.charges_card]; exact hb.1,policy_representatives_card A N q⟩

theorem near_count (b : PolicyBranch A N q sig n) (hq : 0 < q)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q) :
    branchCount b.label n .near ≤ b.chargedNear.card + branchCount b.label n .direct + 1 := by
  classical
  let U := (Finset.range n).filter fun j => b.label j = .near ∧
    ¬ ChargedNear A N q (b.state j) (b.state (j+1))
  have hpartition : branchCount b.label n .near = b.chargedNear.card+U.card := by
    simp only [chargedNear,U,Finset.card_filter,branchCount,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hl : b.label j = .near <;>
      by_cases hc : ChargedNear A N q (b.state j) (b.state (j+1)) <;> simp [hl,hc]
  have hu : U.card ≤ branchCount b.label n .direct+1 := by
    rw [branchCount_card]
    let D := ((Finset.range n).filter fun j => b.label j = .direct)
    have hmap : U.image Nat.succ ⊆ insert n D := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hjn,hn,hc⟩ := Finset.mem_filter.mp hj
      have hjn := Finset.mem_range.mp hjn
      by_cases he : j+1 = n
      · exact Finset.mem_insert.mpr (Or.inl he)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        have hnext := near_uncharged_next_direct hq hceil
          (by simpa only [hn] using b.step j hjn) hc (b.step (j+1) (by omega))
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hnext⟩
    calc
      U.card = (U.image Nat.succ).card := (Finset.card_image_of_injective _ Nat.succ_injective).symm
      _ ≤ (insert n D).card := Finset.card_le_card hmap
      _ ≤ D.card+1 := Finset.card_insert_le _ _
  omega

theorem episode_identity (b : PolicyBranch A N q sig n) :
    (b.state n).angular + branchCount b.label n .far =
      (b.state 0).angular + branchCount b.label n .high := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    have hs := (b.step n (by omega)).episode_balance
    dsimp only [initialSegment] at hp
    rw [branchCount_succ,branchCount_succ]
    omega

theorem far_count (b : PolicyBranch A N q sig n) :
    branchCount b.label n .far ≤ branchCount b.label n .high+1 := by
  have hi := b.episode_identity
  have hzero : (b.state 0).angular ≤ 1 := by cases b.state 0 <;> simp [BranchState.angular]
  omega

theorem suffix_total_decrease (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    (b.state n).finish + branchCount b.label n .suffix*q ≤ (b.state 0).finish := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).nested hq (b.valid n (by omega))
    rw [branchCount_succ,Nat.add_mul]
    by_cases hl : b.label n = .suffix
    · have hd := BranchStep.suffix_decrease (by simpa only [hl] using b.step n (by omega)) hq
        (b.valid n (by omega))
      simp only [hl,ite_true,one_mul]
      omega
    · simp only [hl,ite_false,zero_mul]
      omega

theorem low_total_decrease (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    ((b.state n).finish:ℝ) + (branchCount b.label n .low:ℝ)*(sig*N) ≤ (b.state 0).finish := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).nested hq (b.valid n (by omega))
    have hsR : ((b.state (n+1)).finish:ℝ) ≤ (b.state n).finish := Nat.cast_le.mpr hs.2
    rw [branchCount_succ]
    by_cases hl : b.label n = .low
    · have hd := BranchStep.low_decrease (by simpa only [hl] using b.step n (by omega))
      simp only [hl,ite_true,Nat.cast_add,Nat.cast_one]
      nlinarith
    · simp only [hl,ite_false,add_zero]
      linarith

theorem index_identity (b : PolicyBranch A N q sig n) :
    (b.state n).index = (b.state 0).index + branchCount b.label n .suffix +
      branchCount b.label n .low + branchCount b.label n .far := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).index_change
    rw [branchCount_succ,branchCount_succ,branchCount_succ,hs,hp]
    cases b.label n <;> simp <;> omega

end PolicyBranch

end PlanarFalconer

end OAI
