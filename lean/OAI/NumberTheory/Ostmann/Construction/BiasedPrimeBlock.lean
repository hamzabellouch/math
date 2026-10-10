import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBiasSelection
import OAI.NumberTheory.Ostmann.Construction.TailBudgetNegligible
import OAI.NumberTheory.Ostmann.Construction.DyadicPrimePopulation
import OAI.NumberTheory.Ostmann.Construction.TailPrimeRange

namespace OAI

/-! # A populated dyadic block with actual biases on both summand tails -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem exists_eventual_biased_prime_block (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensEstimate C) (δ : ℝ) (hδ : 0 < δ) (hδU : δ ≤ 1) :
    ∃ a Cpop L₀ : ℝ, 0 < a ∧ 500 ≤ Cpop ∧
      ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, L₀ ≤ L → L ≤ 2 * T ^ 2 →
      T ^ (3 / 2 : ℝ) ≤ L → ∀ hi : ℕ, (hi : ℝ) = Real.exp L →
      ∀ t : ℕ → ℤ,
      δ * T ≤ (∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) *
        |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) →
      ∃ (Z : ℕ) (P : Finset ℕ) (ε : ℕ → ℝ),
        2 ≤ Z ∧ P.Nonempty ∧ P ⊆ logPrimeBand T ∧
        (∀ p ∈ P, Z ≤ p ∧ p < 2 * Z) ∧
        (Z : ℝ) ≤ Cpop * Real.log Z * P.card ∧
        a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) hi).card ∧
        a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) hi).card ∧
        (∀ p ∈ P, (ε p = 1 ∨ ε p = -1) ∧
          (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
          ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3 ∧
          (positiveSummandTail A (summandTailCutoff L) hi).card * (δ / 16) ≤
            ∑ n ∈ positiveSummandTail A (summandTailCutoff L) hi, orientedQuadraticValue ε t n p ∧
          (negativeSummandTail B (summandTailCutoff L) hi).card * (δ / 16) ≤
            ∑ n ∈ negativeSummandTail B (summandTailCutoff L) hi, orientedQuadraticValue (fun p => -ε p) t n p) := by
  obtain ⟨a, ha, hstable⟩ := exists_eventual_stable_summand_tails_at hsize hA hB h N hN C hM.lower
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hstable
  let Cpop := max 500 ((4 + 4 / Real.log 2) / (δ / 4))
  let L₀ := max 1 L₁
  refine ⟨a, Cpop, L₀, ha, le_max_left _ _, ?_⟩
  filter_upwards [eventual_tailDefectBudget_negligible a C (δ / 4) (δ / 4) 1
      (by positivity) (by positivity) (by norm_num),
    eventually_ge_atTop (max 4096 (Real.log 2 + 2 * C))] with T hloss hT
  intro L hL hLU hTL hi hhi t hbias
  have hTbig : 4096 ≤ T := (le_max_left _ _).trans hT
  have hband := logPrimeBand_subset_tailCollisionCutoff T L T hTbig hTL hLU le_rfl
  have hT2 : 2 ≤ T := by linarith
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hdata := hL₁ L ((le_max_right _ _).trans hL) hi hhi
  obtain ⟨hsa, hsb, hselect⟩ := hdata
  let Q := biasedPrimeBand A N T (δ / 4) t
  have hQband : Q ⊆ logPrimeBand T := Finset.filter_subset _ _
  have hQcut : Q ⊆ Nat.primesLE (tailCollisionCutoff L) := hQband.trans hband
  have hodd : ∀ p ∈ Q, p ≠ 2 := by
    intro p hp he
    have hlog := (logPrimeBand_mem (hQband hp)).2.1
    rw [he] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    linarith
  have hQbias : ∀ p ∈ Q, δ / 4 ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))| :=
    fun p hp => (Finset.mem_filter.mp hp).2
  obtain ⟨ε, hweight, hpoint⟩ := hselect Q hQcut hodd (δ / 4) (by positivity) (by linarith) t hQbias
  let R := stableTailPrimes A B N (summandTailCutoff L) hi Q (δ / 4)
  have hRQ : R ⊆ Q := Finset.filter_subset _ _
  have hRband : R ⊆ logPrimeBand T := hRQ.trans hQband
  have hmassQ := biasedPrimeBand_weight A N T δ C t (by linarith)
    ((le_max_right _ _).trans hT) hM hδ.le hbias
  have hlossL := hloss L hL1 hLU
  rw [Real.rpow_one] at hlossL
  have hmassR : (δ / 4) * T ≤ ∑ p ∈ R, Real.log (p : ℝ) / p := by
    linarith only [hweight, hmassQ, hlossL]
  obtain ⟨Z, P, hZ, hP, hPne, hrange, hpop⟩ := exists_populated_prime_block R
    ⌊Real.exp (2 * T)⌋₊ T (δ / 4) (by linarith) (by positivity)
    (fun p hp => (logPrimeBand_mem (hRband hp)).1)
    (fun p hp => Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp (hRband hp)).1)
    (Nat.floor_le (Real.exp_nonneg _)) hmassR
  refine ⟨Z, P, ε, hZ, hPne, hP.trans hRband, hrange, ?_, hsa, hsb, ?_⟩
  · apply hpop.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Z)))
  · intro p hp
    have hh := hpoint p (hP hp)
    simpa only [div_div, show (4 : ℝ) * 4 = 16 by norm_num] using hh

end Ostmann

end OAI
