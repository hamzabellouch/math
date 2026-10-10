import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Jacobsthal.Conclusions.Targets
import OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped BigOperators

def cutoffPrimes (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter Nat.Prime

@[simp] theorem mem_cutoffPrimes {p z : ℕ} :
    p ∈ cutoffPrimes z ↔ p.Prime ∧ p ≤ z := by
  simp only [cutoffPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

def largePrimeFactors (n z : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => z < p

@[simp] theorem mem_largePrimeFactors {n z p : ℕ} :
    p ∈ largePrimeFactors n z ↔ p ∈ n.primeFactors ∧ z < p := by
  simp [largePrimeFactors]

noncomputable def deletionCell (C : Finset ℕ) (a : ℤ) (q : ℕ) : Finset ℕ := by
  classical
  exact C.filter fun i => (q : ℤ) ∣ a + i

@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]

def divisibilityResidue (a : ℤ) (q : ℕ) : ℕ := ((-a) % q).toNat

theorem divisibility_iff_modEq (a : ℤ) {q : ℕ} (hq : 0 < q) (i : ℕ) :
    (q : ℤ) ∣ a + i ↔ Nat.ModEq q i (divisibilityResidue a q) := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hr : ((divisibilityResidue a q : ℕ) : ℤ) = (-a) % q := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hqz))
  rw [← Int.natCast_modEq_iff, hr, Int.ModEq, Int.emod_emod, ← Int.ModEq,
    Int.modEq_iff_dvd]
  have heq : -a - (i : ℤ) = -(a + i) := by ring
  rw [heq, Int.dvd_neg]

theorem card_deletionCell_range (Y : ℕ) (a : ℤ) {q : ℕ} (hq : 0 < q) :
    (deletionCell (Finset.range Y) a q).card =
      Y / q + if divisibilityResidue a q % q < Y % q then 1 else 0 := by
  classical
  unfold deletionCell
  simp_rw [divisibility_iff_modEq a hq]
  rw [← Nat.count_eq_card_filter_range]
  exact Nat.count_modEq_card Y hq (divisibilityResidue a q)

theorem card_deletionCell_le_div_add_one {Y : ℕ} (a : ℤ)
    (C : Finset ℕ) (hC : C ⊆ Finset.range Y) {q : ℕ} (hq : 0 < q) :
    (deletionCell C a q).card ≤ Y / q + 1 := by
  classical
  have hsub : deletionCell C a q ⊆ deletionCell (Finset.range Y) a q := by
    intro i hi
    obtain ⟨hiC, hdiv⟩ := mem_deletionCell.mp hi
    exact mem_deletionCell.mpr ⟨hC hiC, hdiv⟩
  have hcount := Finset.card_le_card hsub
  rw [card_deletionCell_range Y a hq] at hcount
  split_ifs at hcount <;> omega

theorem card_deletionCell_le_real_div_add_one {Y : ℕ} (a : ℤ)
    (C : Finset ℕ) (hC : C ⊆ Finset.range Y) {q : ℕ} (hq : 0 < q) :
    ((deletionCell C a q).card : ℝ) ≤ (Y : ℝ) / q + 1 := by
  calc
    ((deletionCell C a q).card : ℝ) ≤ ((Y / q + 1 : ℕ) : ℝ) := by
      exact_mod_cast card_deletionCell_le_div_add_one a C hC hq
    _ ≤ (Y : ℝ) / q + 1 := by
      push_cast
      exact add_le_add (show ((Y / q : ℕ) : ℝ) ≤ (Y : ℝ) / q from Nat.cast_div_le) le_rfl

noncomputable def cutoffSurvivors (Y z : ℕ) (residue : ℕ → ℕ) : Finset ℕ :=
  SievePartition.survivors (Finset.range Y) (cutoffPrimes z)
    (SievePartition.residueBad residue)

@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto

def CompatibleSmallResidues (n z : ℕ) (a : ℤ) (residue : ℕ → ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ≤ z → residue p % p = divisibilityResidue a p % p

theorem divisibilityResidues_compatible (n z : ℕ) (a : ℤ) :
    CompatibleSmallResidues n z a (divisibilityResidue a) := by
  intro p _ _
  rfl

theorem cutoffSurvivors_avoid_small {Y n z : ℕ} {a : ℤ} {residue : ℕ → ℕ}
    (hcompat : CompatibleSmallResidues n z a residue) :
    ∀ i ∈ cutoffSurvivors Y z residue, ∀ p ∈ n.primeFactors,
      p ≤ z → ¬ (p : ℤ) ∣ a + i := by
  intro i hi p hp hpz hdiv
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hres := (divisibility_iff_modEq a hprime.pos i).mp hdiv
  have hav := (mem_cutoffSurvivors.mp hi).2 p hprime hpz
  apply hav
  rw [hcompat p hp hpz]
  exact hres

noncomputable def coprimeOffsets (Y n : ℕ) (a : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range Y).filter fun i => (a + i).natAbs.Coprime n

@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]

theorem coprime_iff_avoid_primeFactors {n : ℕ} (hn : 0 < n) (x : ℤ) :
    x.natAbs.Coprime n ↔ ∀ p ∈ n.primeFactors, ¬ (p : ℤ) ∣ x := by
  constructor
  · intro hc p hp hpx
    obtain ⟨hprime, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    have hpx' : p ∣ x.natAbs := Int.natCast_dvd.mp hpx
    exact hprime.not_dvd_one (by simpa only [hc.gcd_eq_one] using Nat.dvd_gcd hpx' hpn)
  · intro hav
    apply Nat.coprime_of_dvd
    intro p hp hpx hpn
    exact hav p (Nat.mem_primeFactors.mpr ⟨hp, hpn, ne_of_gt hn⟩)
      (Int.natCast_dvd.mpr hpx)

theorem candidate_subset_coprime_union_deletions
    {Y n z : ℕ} (hn : 0 < n) (a : ℤ) (C : Finset ℕ)
    (hC : C ⊆ Finset.range Y)
    (hsmall : ∀ i ∈ C, ∀ p ∈ n.primeFactors, p ≤ z → ¬ (p : ℤ) ∣ a + i) :
    C ⊆ coprimeOffsets Y n a ∪
      (largePrimeFactors n z).biUnion (deletionCell C a) := by
  classical
  intro i hi
  by_cases hcop : (a + i).natAbs.Coprime n
  · exact Finset.mem_union_left _ (mem_coprimeOffsets.mpr
      ⟨Finset.mem_range.mp (hC hi), hcop⟩)
  · have hbad : ∃ p ∈ n.primeFactors, (p : ℤ) ∣ a + i := by
      by_contra h
      apply hcop
      rw [coprime_iff_avoid_primeFactors hn]
      intro p hp hpi
      exact h ⟨p, hp, hpi⟩
    obtain ⟨p, hp, hpi⟩ := hbad
    have hlarge : z < p := lt_of_not_ge (fun hpz => hsmall i hi p hp hpz hpi)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨p, mem_largePrimeFactors.mpr ⟨hp, hlarge⟩, mem_deletionCell.mpr ⟨hi, hpi⟩⟩)

theorem card_le_coprime_add_large_deletions
    {Y n z : ℕ} (hn : 0 < n) (a : ℤ) (C : Finset ℕ)
    (hC : C ⊆ Finset.range Y)
    (hsmall : ∀ i ∈ C, ∀ p ∈ n.primeFactors, p ≤ z → ¬ (p : ℤ) ∣ a + i) :
    C.card ≤ (coprimeOffsets Y n a).card +
      ∑ q ∈ largePrimeFactors n z, (deletionCell C a q).card := by
  classical
  calc
    C.card ≤ (coprimeOffsets Y n a ∪
        (largePrimeFactors n z).biUnion (deletionCell C a)).card :=
      Finset.card_le_card (candidate_subset_coprime_union_deletions hn a C hC hsmall)
    _ ≤ (coprimeOffsets Y n a).card +
        ((largePrimeFactors n z).biUnion (deletionCell C a)).card := Finset.card_union_le _ _
    _ ≤ (coprimeOffsets Y n a).card +
        ∑ q ∈ largePrimeFactors n z, (deletionCell C a q).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _

theorem exists_coprime_of_survivor_budget
    {Y n z k : ℕ} (hn : 0 < n) (hcard : n.primeFactors.card ≤ k)
    (a : ℤ) (C : Finset ℕ) (hC : C ⊆ Finset.range Y)
    (hsmall : ∀ i ∈ C, ∀ p ∈ n.primeFactors, p ≤ z → ¬ (p : ℤ) ∣ a + i)
    {R : ℝ} (hR : 0 ≤ R)
    (hupper : ∀ q ∈ largePrimeFactors n z, ((deletionCell C a q).card : ℝ) ≤ R)
    (hbudget : (k : ℝ) * R < C.card) :
    ∃ i : ℕ, i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  have hlargecard : (largePrimeFactors n z).card ≤ k :=
    (Finset.card_filter_le _ _).trans hcard
  have hsum : (∑ q ∈ largePrimeFactors n z, ((deletionCell C a q).card : ℝ)) ≤
      (k : ℝ) * R := by
    calc
      _ ≤ ∑ _q ∈ largePrimeFactors n z, R := Finset.sum_le_sum hupper
      _ = ((largePrimeFactors n z).card : ℝ) * R := by simp
      _ ≤ (k : ℝ) * R := mul_le_mul_of_nonneg_right (by exact_mod_cast hlargecard) hR
  have hcountR : (C.card : ℝ) ≤ ((coprimeOffsets Y n a).card : ℝ) +
      ∑ q ∈ largePrimeFactors n z, ((deletionCell C a q).card : ℝ) := by
    exact_mod_cast card_le_coprime_add_large_deletions hn a C hC hsmall
  have hpos : 0 < (coprimeOffsets Y n a).card := by
    have hposR : (0 : ℝ) < (coprimeOffsets Y n a).card := by linarith
    exact_mod_cast hposR
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, mem_coprimeOffsets.mp hi⟩

theorem large_deletionCell_le_cutoff {Y z : ℕ} (a : ℤ)
    (C : Finset ℕ) (hC : C ⊆ Finset.range Y) {q : ℕ} (hqz : z < q) :
    ((deletionCell C a q).card : ℝ) ≤ (Y : ℝ) / (z + 1) + 1 := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le z) hqz
  have hzq : (z : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt hqz
  have hz : (0 : ℝ) < (z : ℝ) + 1 := by positivity
  calc
    ((deletionCell C a q).card : ℝ) ≤ (Y : ℝ) / q + 1 :=
      card_deletionCell_le_real_div_add_one a C hC hq
    _ ≤ (Y : ℝ) / (z + 1) + 1 := by
      exact add_le_add (div_le_div_of_nonneg_left (Nat.cast_nonneg Y) hz hzq) le_rfl

theorem sum_large_deletions_le_elementary {Y n z k : ℕ}
    (hcard : n.primeFactors.card ≤ k) (a : ℤ)
    (C : Finset ℕ) (hC : C ⊆ Finset.range Y) :
    (∑ q ∈ largePrimeFactors n z, ((deletionCell C a q).card : ℝ)) ≤
      (k : ℝ) * ((Y : ℝ) / (z + 1) + 1) := by
  have hlargecard : (largePrimeFactors n z).card ≤ k :=
    (Finset.card_filter_le _ _).trans hcard
  calc
    _ ≤ ∑ _q ∈ largePrimeFactors n z, ((Y : ℝ) / (z + 1) + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      exact large_deletionCell_le_cutoff a C hC (mem_largePrimeFactors.mp hq).2
    _ = ((largePrimeFactors n z).card : ℝ) * ((Y : ℝ) / (z + 1) + 1) := by simp [mul_add]
    _ ≤ (k : ℝ) * ((Y : ℝ) / (z + 1) + 1) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hlargecard)
      positivity

theorem exists_coprime_of_cutoff_estimates
    {Y n z k : ℕ} (hn : 0 < n) (hcard : n.primeFactors.card ≤ k)
    (a : ℤ) (residue : ℕ → ℕ)
    (hcompat : CompatibleSmallResidues n z a residue)
    {S R : ℝ} (hR : 0 ≤ R)
    (hlower : S ≤ (cutoffSurvivors Y z residue).card)
    (hupper : ∀ q ∈ largePrimeFactors n z,
      ((deletionCell (cutoffSurvivors Y z residue) a q).card : ℝ) ≤ R)
    (hbudget : (k : ℝ) * R < S) :
    ∃ i : ℕ, i < Y ∧ (a + i).natAbs.Coprime n := by
  apply exists_coprime_of_survivor_budget hn hcard a (cutoffSurvivors Y z residue)
  · intro i hi
    exact Finset.mem_range.mpr (mem_cutoffSurvivors.mp hi).1
  · exact cutoffSurvivors_avoid_small hcompat
  · exact hR
  · exact hupper
  · exact hbudget.trans_le hlower

theorem isJacobsthalBound_of_cutoff_estimates
    (Y z k : ℕ) {S R : ℝ} (hR : 0 ≤ R)
    (hlower : ∀ residue : ℕ → ℕ, S ≤ (cutoffSurvivors Y z residue).card)
    (hupper : ∀ (residue : ℕ → ℕ) (a : ℤ) (q : ℕ), q.Prime → z < q →
      ((deletionCell (cutoffSurvivors Y z residue) a q).card : ℝ) ≤ R)
    (hbudget : (k : ℝ) * R < S) :
    Targets.IsJacobsthalBound k Y := by
  intro n hn hcard a
  apply exists_coprime_of_cutoff_estimates hn hcard a (divisibilityResidue a)
    (divisibilityResidues_compatible n z a) hR (hlower _)
  · intro q hq
    obtain ⟨hqn, hqz⟩ := mem_largePrimeFactors.mp hq
    exact hupper _ a q (Nat.mem_primeFactors.mp hqn).1 hqz
  · exact hbudget

end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI
