import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeRanges
import OAI.NumberTheory.Ostmann.Construction.ScheduledPageAvoidance
import OAI.NumberTheory.Ostmann.Construction.WholeShellRetainedLinearMass

namespace OAI

/-! # Prime and mass data for every actual selected prior -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem initialRegularPrimeRange_upper (L : ℝ) (p : ℕ)
    (hp : p ∈ initialRegularPrimeRange L) :
    (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L)) := by
  have h := (Nat.mem_primesLE.mp hp).1
  have h' : (p : ℝ) ≤ ⌊Real.exp (Real.exp ((11 / 1000 : ℝ) * L))⌋₊ := by
    exact_mod_cast h
  exact h'.trans (Nat.floor_le (Real.exp_nonneg _))

theorem selected_regular_alphabet_nonempty
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top) :
    (initialRegularPrimeRange L).Nonempty := by
  have hmass := htop.2.2.2.2.1
  have hne : (selectedTailCellPrimes A B N Y hi D top).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, lt_self_iff_false] at hmass
  exact hne.mono htop.subset_initialRegularPrimeRange

theorem selected_bulk_prime_range (L : ℝ) (hL : 0 ≤ L) (D : Finset ℕ) :
    let Qb := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
      (Real.exp ((6 / 1000 : ℝ) * L)) \ D
    Qb ⊆ initialRegularPrimeRange L ∧
      ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
  intro Qb
  refine ⟨initial_broad_cell_subset L (4 / 1000) (6 / 1000) hL (by norm_num) D, ?_⟩
  intro p hp
  obtain ⟨hprime, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp (Finset.mem_sdiff.mp hp).1
  have hl : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((4 / 1000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [hL]))
  exact hl.trans ((Real.lt_log_iff_exp_lt (by exact_mod_cast hprime.pos)).mp hlo).le

theorem eventual_selected_bulk_mass {C : ℝ} (hM : MertensEstimate C) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, D.card ≤ 2 →
      1 / Real.exp (2 * L) ≤
        ∑ p ∈ primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ D, (p : ℝ)⁻¹ := by
  filter_upwards [whole_shell_retained_linear_mass hM 1 (by norm_num),
    eventually_ge_atTop (16000 : ℝ)] with L hmass hL D hD
  have hcard : (D.card : ℝ) ≤ Real.exp (1 * L) := by
    rw [one_mul]
    have hd : (D.card : ℝ) ≤ 2 := by exact_mod_cast hD
    have he := Real.add_one_le_exp L
    nlinarith only [hd, he, hL]
  apply le_trans _ (hmass D hcard)
  have he : Real.exp (-(2 * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [one_div, ← Real.exp_neg]
  linarith

theorem selected_schedule_prime_data
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (hbulkmass : 1 / Real.exp (2 * L) ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹) :
    (∀ j, completedCompensationSets A B N Y hi D top cs j ⊆ initialRegularPrimeRange L ∧
      1 / Real.exp (2 * L) ≤ ∑ p ∈ completedCompensationSets A B N Y hi D top cs j, (p : ℝ)⁻¹) ∧
    (∀ j p, p ∈ completedCompensationSets A B N Y hi D top cs j →
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (p : ℝ)) ∧
    (∀ n m offset (i : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m),
      let Q := scheduledRegularPrimeSets (selectedTailCellPrimes A B N Y hi D)
        Qb top (cs.drop offset) n m i
      Q ⊆ initialRegularPrimeRange L ∧
      1 / Real.exp (2 * L) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹) ∧
    (∀ n m offset (i : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m),
      ∀ p, p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N Y hi D)
        Qb top (cs.drop offset) n m i →
        Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ)) := by
  have he : 1 / Real.exp (2 * L) = Real.exp (-(2 * L)) := by
    rw [one_div, Real.exp_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hd := completedCompensationPrior_data htop hcs (initialRegularPrimeRange L)
      (fun _ h => h) j
    exact ⟨hd.1, he ▸ hd.2.1⟩
  · intro j p hp
    exact (completedCompensationSets_range htop hcs hlower j p hp).2
  · intro n m offset i
    have hd := scheduledRegularPrimeSets_sub_mass htop hcs (initialRegularPrimeRange L)
      (fun _ h => h) hbulk (he ▸ hbulkmass) n m offset i
    exact ⟨hd.1, he ▸ hd.2⟩
  · intro n m offset i p hp
    exact (scheduledRegularPrimeSets_range htop hcs hL hlower hbulk hbulklower
      n m offset i p hp).2

end Ostmann

end OAI
