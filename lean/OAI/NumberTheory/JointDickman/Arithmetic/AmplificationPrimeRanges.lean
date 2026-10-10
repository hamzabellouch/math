import OAI.NumberTheory.JointDickman.Arithmetic.PrimeRangeOperators
import OAI.NumberTheory.JointDickman.Counting.AdditionRatioWindow
import OAI.NumberTheory.JointDickman.Probability.AmplificationHighCoins

namespace OAI

/-! # The actual low and high prime ranges used by the second split -/

namespace JointDickman

open Finset

noncomputable def upperAdditionPrimes (B : ℕ) (Y : ℝ) : Finset ℕ :=
  auxiliaryPrimes B \ additionPrimes B Y

theorem additionPrimes_eq_filter (B : ℕ) (Y : ℝ) :
    additionPrimes B Y = (auxiliaryPrimes B).filter (fun p : ℕ => Real.log p ≤ Y) := by
  classical
  ext p
  constructor
  · intro hp
    have haux := additionPrimes_subset_auxiliary B Y hp
    refine mem_filter.mpr ⟨haux, ?_⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (additionPrimes_prime B Y p hp).pos
    apply (Real.log_le_iff_le_exp hp0).mpr
    have hh := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1
    exact (Nat.le_floor_iff (Real.exp_pos _).le).mp hh |>.trans
      (Real.exp_le_exp.mpr (min_le_left _ _))
  · intro hp
    obtain ⟨haux, hlog⟩ := mem_filter.mp hp
    have hprime := auxiliaryPrimes_prime B p haux
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hu : (p : ℝ) ≤ Real.exp (4 * (B : ℝ)) := by
      exact (Nat.le_floor_iff (Real.exp_pos _).le).mp
        (Nat.mem_primesLE.mp (mem_filter.mp haux).1).1
    have hy : (p : ℝ) ≤ Real.exp Y := (Real.log_le_iff_le_exp hp0).mp hlog
    have hmin : (p : ℝ) ≤ Real.exp (min Y (4 * B)) := by
      rcases le_total Y (4 * (B : ℝ)) with h | h
      · simpa only [min_eq_left h] using hy
      · simpa only [min_eq_right h] using hu
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hmin, hprime⟩, (mem_filter.mp haux).2⟩

theorem additionPrimeRanges_disjoint (B : ℕ) (Y : ℝ) :
    Disjoint (additionPrimes B Y) (upperAdditionPrimes B Y) := disjoint_sdiff_self_right

theorem additionPrimeRanges_union (B : ℕ) (Y : ℝ) :
    additionPrimes B Y ∪ upperAdditionPrimes B Y = auxiliaryPrimes B :=
  union_sdiff_of_subset (additionPrimes_subset_auxiliary B Y)

theorem selected_upperAdditionPrimes {B : ℕ} {Y : ℝ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : A ∩ upperAdditionPrimes B Y = highPrimePart Y A := by
  classical
  ext p
  simp only [upperAdditionPrimes, additionPrimes_eq_filter, mem_inter, mem_sdiff,
    mem_filter, highPrimePart]
  constructor
  · rintro ⟨ha, _, hn⟩
    exact ⟨ha, lt_of_not_ge (fun h => hn ⟨hA ha, h⟩)⟩
  · rintro ⟨ha, hh⟩
    exact ⟨ha, hA ha, fun h => not_le_of_gt hh h.2⟩

theorem selected_additionPrimeRanges_union {B : ℕ} {Y : ℝ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    (A ∩ additionPrimes B Y) ∪ (A ∩ upperAdditionPrimes B Y) = A := by
  rw [← inter_union_distrib_left, additionPrimeRanges_union, inter_eq_left.mpr hA]

end JointDickman

end OAI
