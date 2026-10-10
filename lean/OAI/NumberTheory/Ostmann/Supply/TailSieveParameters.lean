import OAI.NumberTheory.Ostmann.Preliminaries.TailLogImbalance
import OAI.NumberTheory.Ostmann.Supply.SieveBudgetParameters
import OAI.NumberTheory.Ostmann.Characters.SparseBandMass

namespace OAI

/-! # The actual tail budget at the square-root sieve scale

The auxiliary collision estimate may be applied at `Y = X²`: its supports
are the same fixed infinite-tail residue sets. This choice keeps the endpoint
integral when `X` is integral and covers every prime up to `sqrt X`.
-/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem tailDefectBudget_doubled_exp (a C L : ℝ) :
    tailDefectBudget a C (2 * Real.exp L) =
      20 * L + (24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a) := by
  unfold tailDefectBudget
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem eventual_sqrt_cutoff_le_tail :
    ∀ᶠ L : ℝ in atTop,
      ⌊Real.exp (Real.exp L / 2)⌋₊ ≤ tailCollisionCutoff (2 * Real.exp L) := by
  have hsmall := eventual_affine_log_le_rpow 5 (Real.log 2) (1 / 6) 1
    (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hsmall
  have hlim : Tendsto (fun L : ℝ => 2 * Real.exp L) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (by norm_num)
  filter_upwards [hlim.eventually (eventual_tailCollisionCutoff 0),
    hlim.eventually hsmall] with L hcut hsmall
  have hb := tailCollisionCutoff_bounds (2 * Real.exp L) hcut.1 hcut.2.1
  have hQ : (0 : ℝ) < tailCollisionCutoff (2 * Real.exp L) := by
    exact_mod_cast hb.1
  have hlog : Real.exp L / 2 ≤ Real.log (tailCollisionCutoff (2 * Real.exp L) : ℝ) := by
    linarith [hb.2.2, Real.exp_pos L]
  have he := (Real.exp_le_exp.mpr hlog)
  rw [Real.exp_log hQ] at he
  exact (Nat.floor_le_floor he).trans_eq (Nat.floor_natCast _)

theorem logLogPrimeBand_subset_sqrt_cutoff (L : ℝ) (hL : 10 ≤ L) :
    logLogPrimeBand L ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ := by
  intro p hp
  obtain ⟨hpp, _, hlog⟩ := logLogPrimeBand_mem hp
  have hhalf : Real.exp ((9 / 10 : ℝ) * L) ≤ Real.exp L / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * L) := by
      linarith [Real.add_one_le_exp ((1 / 10 : ℝ) * L)]
    have hm := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg ((9 / 10 : ℝ) * L))
    rw [← Real.exp_add] at hm
    have hid : (9 / 10 : ℝ) * L + (1 / 10 : ℝ) * L = L := by ring
    rw [hid] at hm
    linarith
  refine Nat.mem_primesLE.mpr ⟨Nat.le_floor ?_, hpp⟩
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hpp.pos)).mp (hlog.trans hhalf)

theorem EventuallyPrimeSumset.sqrt_scale_logarithmic_imbalance_with_disjoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ^ 2 ≤
        4 * (20 * L + (24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a)) *
          primeReciprocalLogConstant C := by
  obtain ⟨N, hN, a, ha, hbudget⟩ := h.tail_logarithmic_imbalance_with_disjoint hsize hA hB C hM
  refine ⟨N, hN, a, ha, ?_⟩
  have hlim : Tendsto (fun L : ℝ => 2 * Real.exp L) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop (by norm_num)
  filter_upwards [hlim.eventually hbudget, eventual_sqrt_cutoff_le_tail] with L hb hcut
  intro X hX P hP
  have hXsq : ((X ^ 2 : ℕ) : ℝ) = Real.exp (2 * Real.exp L) := by
    rw [Nat.cast_pow, hX, ← Real.exp_nat_mul]
    norm_num
  have hsub : P ⊆ Nat.primesLE (tailCollisionCutoff (2 * Real.exp L)) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE (hP hp)).trans hcut,
      Nat.prime_of_mem_primesLE (hP hp)⟩
  simpa only [tailDefectBudget_doubled_exp] using hb (X ^ 2) hXsq P hsub

theorem eventual_affine_square_budget (d e : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, W ^ 2 ≤ d * L + e →
      W ≤ L ^ (3 / 4 : ℝ) / 16 := by
  filter_upwards [eventual_square_budget_le_three_quarters (|d| + |e|),
    eventually_ge_atTop (1 : ℝ)] with L hnum hL W hW
  apply hnum W
  have hd := mul_le_mul_of_nonneg_right (le_abs_self d) (by linarith : 0 ≤ L)
  have he := mul_le_mul_of_nonneg_left hL (abs_nonneg e)
  linarith [le_abs_self e]

/-- The exact `L^(3/4)/16` budget for the multiplier count
on the infinite-tail residue supports. -/
theorem EventuallyPrimeSumset.sqrt_scale_sieve_log_budget_with_disjoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, (∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p)) ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ≤
          L ^ (3 / 4 : ℝ) / 16 := by
  obtain ⟨N, hN, a, _, hb⟩ := h.sqrt_scale_logarithmic_imbalance_with_disjoint hsize hA hB C hM
  let d := 80 * primeReciprocalLogConstant C
  let e := 4 * (24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a) *
    primeReciprocalLogConstant C
  refine ⟨N, hN, ?_⟩
  filter_upwards [hb, eventual_affine_square_budget d e] with L hb hnum X hX P hP
  apply hnum
  convert hb X hX P hP using 1
  dsimp [d, e]
  ring

theorem EventuallyPrimeSumset.sqrt_scale_logarithmic_imbalance
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ^ 2 ≤
        4 * (20 * L + (24 * Real.log 2 + 4 * C + 2 * Real.log 4 / a)) *
          primeReciprocalLogConstant C := by
  obtain ⟨N, _, a, ha, hb⟩ := h.sqrt_scale_logarithmic_imbalance_with_disjoint hsize hA hB C hM
  exact ⟨N, a, ha, hb⟩

theorem EventuallyPrimeSumset.sqrt_scale_sieve_log_budget
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensEstimate C) :
    ∃ N : ℕ, ∀ᶠ L : ℝ in atTop,
      ∀ X : ℕ, (X : ℝ) = Real.exp (Real.exp L) →
      ∀ P : Finset ℕ, P ⊆ Nat.primesLE ⌊Real.exp (Real.exp L / 2)⌋₊ →
      (∑ p ∈ P, |Real.log
        (((Finset.range p \ tailSupport A N p).card : ℝ) / (tailSupport A N p).card)| / p) ≤
          L ^ (3 / 4 : ℝ) / 16 := by
  obtain ⟨N, _, hb⟩ := h.sqrt_scale_sieve_log_budget_with_disjoint hsize hA hB C hM
  exact ⟨N, hb⟩

end Ostmann

end OAI
