import OAI.NumberTheory.Ostmann.Preliminaries.UniformTailStability
import OAI.NumberTheory.Ostmann.Construction.RoundedTailScale
import OAI.NumberTheory.Ostmann.Construction.TypicalTailAssembly
import OAI.NumberTheory.Ostmann.Supply.CollisionPrimeCellBudget
import OAI.NumberTheory.Ostmann.Construction.TailFourierMass
import OAI.NumberTheory.Ostmann.Characters.HigherCharacterDecorrelation

namespace OAI

/-! # Unbalanced tail supports have negligible mass on each harmonic band -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem EventuallyPrimeSumset.eventual_unbalanced_band_mass
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (α β ε : ℝ) (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      (∑ p ∈ P.filter (fun p => ¬((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
        residueDensity (tailDensityMask A N p) ≤ 2 / 3)), (p : ℝ)⁻¹) ≤ ε * L := by
  classical
  obtain ⟨a, ha, hcounts⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (hcounts.and ((eventual_tailCollisionCutoff N).and eventual_endpointTestCutoff_quarter))
  have herr := eventual_endpoint_test_error_small α (β + 1) (Real.log 1000)
    (C + Real.log 4 / (2 * a)) 1 ε hα (by norm_num) hε
  filter_upwards [eventual_rounded_tail_scale β hβ T₀, herr, eventually_ge_atTop (1 : ℝ)]
    with L hround herr hL P hP
  obtain ⟨X, T, hT, hX, hlogT, hrange⟩ := hround
  obtain ⟨hcounts, hcut, hquarter⟩ := hT₀ T hT
  obtain ⟨hEA, hEB, _, _, _⟩ := hcounts X hX
  let EA := summandTail A (summandTailCutoff T) X
  let EB := summandTail B (summandTailCutoff T) X
  let S := tailSupport A N
  let V := fun p => Finset.range p \ S p
  let μ := fun p => residueMass EA (fun _ => 1 / (EA.card : ℝ)) p
  let ν := fun p => fiberMass EB (fun _ => 1 / (EB.card : ℝ)) (negativeResidue p)
  let D := 20 * Real.log T + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime :=
    ((mem_closedLogLogPrimeBand_iff α β L p).mp (hP hp)).1
  have hPcut : P ⊆ Nat.primesLE (tailCollisionCutoff T) := by
    intro p hp
    have hpband := (mem_closedLogLogPrimeBand_iff α β L p).mp (hP hp)
    have hpupper := prime_of_loglog_upper p hpband.1 _ hpband.2.2
    have hcutupper : Real.exp (Real.exp (β * L)) ≤ tailCollisionCutoff T :=
      (Real.exp_le_exp.mpr hrange).trans (hquarter.trans (by exact_mod_cast
        (endpointTestCutoff_le_tailCollisionCutoff T hcut.1)))
    exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpupper.trans hcutupper, hpband.1⟩
  have hS (p : ℕ) (hp : p ∈ P) : (S p).Nonempty := tailSupport_nonempty hA N p (hprime p hp).pos
  have hV (p : ℕ) (hp : p ∈ P) : (V p).Nonempty :=
    tailSupport_complement_nonempty hB (hprime p hp).pos (hN p (hprime p hp))
  have hcard (p : ℕ) : (S p).card + (V p).card = p := tailSupport_card_add_complement A N p
  have hbudget : (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (V p) (μ p) (ν p)) ≤ D := by
    have hh := uniform_tail_collision_bound hA hB N (summandTailCutoff T) X a T C ha hcut.1
      hcut.2.1 hX hcut.2.2 (fun p hp => hN p (Nat.prime_of_mem_primesLE hp))
      (by simpa only [positiveSummandTail_card] using hEA)
      (by simpa only [negativeSummandTail_card] using hEB) hM
    apply le_trans _ hh
    exact Finset.sum_le_sum_of_subset_of_nonneg hPcut (fun p hp _ =>
      mul_nonneg (Real.log_natCast_nonneg p)
        (collisionDefect_nonneg _ _ _ _
          (tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos)
          (tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos
            (hN p (Nat.prime_of_mem_primesLE hp))) (hcard p).le))
  let E := collisionExceptionalPrimes P S V μ ν
  let Bad := P.filter (fun p => ¬((1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N p) ∧
    residueDensity (tailDensityMask A N p) ≤ 2 / 3))
  have hBad : Bad ⊆ E := by
    intro p hp
    obtain ⟨hpP, hnot⟩ := Finset.mem_filter.mp hp
    by_contra hpE
    have hbal := collision_retained_prime_balanced P S V μ ν hS hV (fun p _ => hcard p) p
      (Finset.mem_sdiff.mpr ⟨hpP, hpE⟩)
    exact hnot ((tailDensityMask_balanced_iff A N p (hprime p hpP).pos).mpr hbal)
  have hmass : (∑ p ∈ Bad, (p : ℝ)⁻¹) ≤ 4 * D / Real.exp (α * L) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hlogmass := collisionExceptionalPrimes_log_mass P S V μ ν D hprime hS hV
      (fun p _ => (hcard p).le) hbudget
    calc
      _ = ∑ p ∈ Bad, Real.exp (α * L) * (p : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intros
        ring
      _ ≤ ∑ p ∈ Bad, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        have hb := (mem_closedLogLogPrimeBand_iff α β L p).mp
          (hP (Finset.mem_filter.mp hp).1)
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast hb.1.one_lt
        have hh := (Real.le_log_iff_exp_le (Real.log_pos hp1)).mp hb.2.1
        simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ ∑ p ∈ E, Real.log (p : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hBad (fun p _ _ =>
          div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
      _ ≤ _ := hlogmass
  have hD : D ≤ 48 * Real.log T + 4 * (C + Real.log 4 / (2 * a)) +
      4 * Real.log 2 + 2 * Real.log 4 := by
    have hlog0 := Real.log_nonneg hcut.1
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp only [D]
    have he : 4 * (Real.log 4 / (2 * a)) = 2 * Real.log 4 / a := by ring
    rw [mul_add, he]
    linarith only [hlog0, hlog4]
  have he := herr T hlogT
  norm_num only [one_pow, one_mul] at he
  have hfinal : 4 * D / Real.exp (α * L) < ε := by
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hD (Real.exp_nonneg (α * L))) (show (0 : ℝ) ≤ 4 by norm_num)
    calc
      _ = 4 * (D / Real.exp (α * L)) := by ring
      _ ≤ _ := hh
      _ < ε := he
  exact hmass.trans (hfinal.le.trans (le_mul_of_one_le_right hε.le hL))

end Ostmann

end OAI
