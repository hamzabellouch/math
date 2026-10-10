import OAI.NumberTheory.JointDickman.Probability.TwoSiteSplitModel
import OAI.NumberTheory.JointDickman.Amplification.DyadicChangeScales

namespace OAI

/-! # Locating and orienting the largest changed prime -/

namespace JointDickman

open Finset

noncomputable def twoSiteChangeSet {P : Finset ℕ} (x : TwoSiteSplit P) : Finset ℕ :=
  (symmDiff x.first₁.val x.second₁.val) ∪ (symmDiff x.first₂.val x.second₂.val)

def twoSiteNoChange {P : Finset ℕ} (x : TwoSiteSplit P) : Prop :=
  x.first₁ = x.second₁ ∧ x.first₂ = x.second₂

def twoSiteNoHighChange {P : Finset ℕ} (x : TwoSiteSplit P) (Y : ℝ) : Prop :=
  ∀ p ∈ twoSiteChangeSet x, Real.log p ≤ Y

def twoSiteAddition {P : Finset ℕ} (x : TwoSiteSplit P) (Y : ℝ) (site : Bool) : Prop :=
  ∃ p ∈ (if site then x.second₂.val \ x.first₂.val else x.second₁.val \ x.first₁.val),
    Y / 2 < Real.log p

theorem twoSiteChangeSet_subset {P : Finset ℕ} (x : TwoSiteSplit P) : twoSiteChangeSet x ⊆ P := by
  intro p hp
  rcases mem_union.mp hp with h | h
  · rcases mem_symmDiff.mp h with h | h
    · exact mem_powerset.mp x.first₁.property h.1
    · exact mem_powerset.mp x.second₁.property h.1
  · rcases mem_symmDiff.mp h with h | h
    · exact mem_powerset.mp x.first₂.property h.1
    · exact mem_powerset.mp x.second₂.property h.1

theorem twoSiteChangeSet_eq_empty {P : Finset ℕ} (x : TwoSiteSplit P) :
    twoSiteChangeSet x = ∅ ↔ twoSiteNoChange x := by
  simp only [twoSiteChangeSet, union_eq_empty, symmDiff_eq_empty, twoSiteNoChange, Subtype.ext_iff]

theorem twoSiteChangeSet_swap {P : Finset ℕ} (x : TwoSiteSplit P) :
    twoSiteChangeSet x.swap = twoSiteChangeSet x := by
  simp only [twoSiteChangeSet, TwoSiteSplit.swap, symmDiff_comm]

theorem twoSiteNoHighChange_swap {P : Finset ℕ} (x : TwoSiteSplit P) (Y : ℝ) :
    twoSiteNoHighChange x.swap Y ↔ twoSiteNoHighChange x Y := by
  unfold twoSiteNoHighChange
  rw [twoSiteChangeSet_swap]

/-- At the largest changed prime, at least one orientation is an addition
at one of the two sites. -/
theorem twoSite_change_orientations {P : Finset ℕ} (x : TwoSiteSplit P) {p : ℕ} {Y : ℝ}
    (hp : p ∈ twoSiteChangeSet x) (hY : Y / 2 < Real.log p) :
    twoSiteAddition x Y false ∨ twoSiteAddition x Y true ∨
      twoSiteAddition x.swap Y false ∨ twoSiteAddition x.swap Y true := by
  rcases mem_union.mp hp with h | h
  · rcases mem_symmDiff.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨p, mem_sdiff.mpr h, hY⟩))
    · exact Or.inl ⟨p, mem_sdiff.mpr h, hY⟩
  · rcases mem_symmDiff.mp h with h | h
    · exact Or.inr (Or.inr (Or.inr ⟨p, mem_sdiff.mpr h, hY⟩))
    · exact Or.inr (Or.inl ⟨p, mem_sdiff.mpr h, hY⟩)

/-- Every nontrivial change belongs to a single covered dyadic interval;
the prime at its top gives one of the four addition orientations. -/
theorem largest_changed_prime_shell {B N : ℕ}
    (hB : 1 < B) (hcap : 4 * (B : ℝ) ≤ (2 : ℝ)^N * Real.log (auxiliaryCutoff B))
    (x : TwoSiteSplit (auxiliaryPrimes B)) (hx : ¬ twoSiteNoChange x) :
    ∃ i ∈ Icc 1 N, twoSiteNoHighChange x (primeTailEndpoint B i) ∧
      (twoSiteAddition x (primeTailEndpoint B i) false ∨ twoSiteAddition x (primeTailEndpoint B i) true ∨
        twoSiteAddition x.swap (primeTailEndpoint B i) false ∨ twoSiteAddition x.swap (primeTailEndpoint B i) true) := by
  classical
  have hne : (twoSiteChangeSet x).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    exact hx ((twoSiteChangeSet_eq_empty x).mp he)
  let p := (twoSiteChangeSet x).max' hne
  have hp : p ∈ twoSiteChangeSet x := max'_mem _ hne
  have hpP := twoSiteChangeSet_subset x hp
  have hprime := auxiliaryPrimes_prime B p hpP
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by exact_mod_cast pow_pos (Nat.zero_lt_of_lt hB) 1000
  have hL : 0 < Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  have hlo : Real.log (auxiliaryCutoff B) < Real.log p :=
    Real.log_lt_log hP0 (mem_filter.mp hpP).2
  have hhi : Real.log p ≤ 4 * (B : ℝ) := by
    apply (Real.log_le_iff_le_exp hp0).mpr
    exact (Nat.le_floor_iff (Real.exp_pos _).le).mp (Nat.mem_primesLE.mp (mem_filter.mp hpP).1).1
  obtain ⟨i, hi, hilow, hiup⟩ := dyadic_shell_cover hL hlo (hhi.trans hcap)
  refine ⟨i, hi, ?_, twoSite_change_orientations x hp hilow⟩
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (auxiliaryPrimes_prime B q (twoSiteChangeSet_subset x hq)).pos
  have hqp : q ≤ p := le_max' _ q hq
  exact (Real.log_le_log hq0 (by exact_mod_cast hqp)).trans hiup

end JointDickman

end OAI
