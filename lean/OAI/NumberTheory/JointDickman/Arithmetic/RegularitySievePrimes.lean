import OAI.NumberTheory.JointDickman.Arithmetic.TiltedSieveDensity
import OAI.NumberTheory.JointDickman.Arithmetic.RegularityTailPrimeSums

namespace OAI

/-! # Identification of the sieve's actual prefix prime sets -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem good_prefix_sieve_set (P Z : ℕ) {U : ℝ} (hP : 6 ≤ P)
    (hU : 0 ≤ U) (hUZ : U ≤ Z) :
    (sievePrimes Z).filter (fun p => P < p ∧ p ∈ largePrimeSet U P) = largePrimeSet U P := by
  classical
  ext p
  constructor
  · intro hp
    exact (mem_filter.mp hp).2.2
  · intro hp
    obtain ⟨hpU, hpP⟩ := mem_filter.mp hp
    obtain ⟨hpU, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hpZ : p ≤ Z := by
      have hpr : (p : ℝ) ≤ U := (Nat.le_floor_iff hU).mp hpU
      exact_mod_cast hpr.trans hUZ
    have hPp : P < p := by exact_mod_cast hpP
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩, ⟨hPp, hp⟩⟩

theorem full_prefix_sieve_set (P Z : ℕ) {U : ℝ} (hP : 6 ≤ P) (hZU : (Z : ℝ) ≤ U) :
    (sievePrimes Z).filter (fun p => P < p ∧ p ∈ largePrimeSet U P) = largePrimeSet Z P := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, hpP, _⟩ := mem_filter.mp hp
    obtain ⟨hpZ, _⟩ := mem_filter.mp hpS
    apply mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Nat.floor_natCast] using hpZ
    · exact_mod_cast hpP
  · intro hp
    obtain ⟨hpZ, hpP⟩ := mem_filter.mp hp
    rw [Nat.floor_natCast] at hpZ
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hPp : P < p := by exact_mod_cast hpP
    have hpU : p ≤ ⌊U⌋₊ := Nat.le_floor ((by exact_mod_cast hpZ : (p : ℝ) ≤ Z).trans hZU)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩,
      ⟨hPp, mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpU, hprime⟩, hpP⟩⟩⟩

theorem primePrefix_eq_largePrimeSet {B : ℕ} (hB : 1 ≤ B) {g : ℝ} (hg : g < 1) :
    primePrefix B g (auxiliaryPrimes B) =
      largePrimeSet (Real.exp ((B : ℝ) ^ g)) (auxiliaryCutoff B) := by
  classical
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpower : (B : ℝ) ^ g ≤ 4 * B := by
    have h := Real.rpow_le_rpow_of_exponent_le hB1 hg.le
    rw [Real.rpow_one] at h
    linarith
  have hupper : Real.exp ((B : ℝ) ^ g) ≤ auxiliaryUpper B := Real.exp_le_exp.mpr hpower
  rw [primePrefix, ite_eq_left hg]
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hplog⟩ := mem_filter.mp hp
    obtain ⟨hpU, hpCut⟩ := mem_filter.mp hpP
    obtain ⟨_, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpX : (p : ℝ) ≤ Real.exp ((B : ℝ) ^ g) := by
      simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hplog
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpX, hprime⟩, hpCut⟩
  · intro hp
    obtain ⟨hpU, hpCut⟩ := mem_filter.mp hp
    obtain ⟨hpU, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpX : (p : ℝ) ≤ Real.exp ((B : ℝ) ^ g) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mp hpU
    have hpUpper : p ≤ ⌊auxiliaryUpper B⌋₊ := Nat.le_floor (hpX.trans hupper)
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpUpper, hprime⟩, hpCut⟩, ?_⟩
    simpa only [Real.log_exp] using Real.log_le_log hp0 hpX

theorem prefix_endpoint_le_sieveCutoff {c g : ℝ} (hc : 0 < c) (hg : g < 1) :
    ∀ᶠ B : ℕ in atTop, Real.exp ((B : ℝ) ^ g) ≤ sieveCutoff c B := by
  have hlim : Tendsto (fun B : ℕ => (B : ℝ) ^ g / B) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (power_div_power_tendsto_zero hg).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by linarith : (0 : ℝ) < c / 2)),
    sieveCutoff_eventually hc, eventually_gt_atTop 0] with B hsmall hcut hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ g ≤ Real.log (sieveCutoff c B) := by
    have h := (div_le_iff₀ hB0).mp hsmall
    exact h.trans hcut.2.2.1
  have hZ : (0 : ℝ) < sieveCutoff c B := by exact_mod_cast (by omega : 0 < sieveCutoff c B)
  simpa only [Real.exp_log hZ] using Real.exp_le_exp.mpr hpow

/-- This is the actual reciprocal mass appearing in the tilted sieve,
including its finite cutoff, for every fixed regularity-grid point. -/
theorem tilt_prefix_mass_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c g : ℝ}
    (hc : 0 < c) (hc4 : c ≤ 4) (hg : 0 < g) (hg1 : g ≤ 1) :
    Tendsto (fun B : ℕ =>
      tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
        (primePrefix B g (auxiliaryPrimes B)) / auxiliaryLogLength B) atTop (𝓝 g) := by
  by_cases hglt : g < 1
  · have h := regularity_prefix_prime_sum_tendsto hM (by norm_num : (0 : ℝ) < 1) hg
    apply h.congr'
    filter_upwards [prefix_endpoint_le_sieveCutoff hc hglt,
      auxiliaryCutoff_tendsto.eventually_ge_atTop 6, eventually_ge_atTop 1] with B hX hP hB
    rw [one_mul, primePrefix_eq_largePrimeSet hB hglt]
    unfold tiltPrimeReciprocalMass
    rw [good_prefix_sieve_set _ _ hP (Real.exp_pos _).le hX]
  · have hg_eq : g = 1 := le_antisymm hg1 (le_of_not_gt hglt)
    subst g
    have h := regularity_prefix_prime_sum_tendsto hM hc (by norm_num : (0 : ℝ) < 1)
    apply h.congr'
    filter_upwards [sieveCutoff_eventually hc, auxiliaryCutoff_tendsto.eventually_ge_atTop 6] with B hcut hP
    have hZU : (sieveCutoff c B : ℝ) ≤ auxiliaryUpper B := by
      refine hcut.2.2.2.trans (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_right hc4 (Nat.cast_nonneg B)
    simp only [Real.rpow_one, primePrefix, lt_self_iff_false, ite_false]
    unfold tiltPrimeReciprocalMass auxiliaryPrimes
    rw [full_prefix_sieve_set _ _ hP hZU]
    simp only [largePrimeSet, Nat.floor_natCast, sieveCutoff]

open Classical in
theorem tail_sieve_set (B Z : ℕ) {Y : ℝ} (hP : 6 ≤ auxiliaryCutoff B)
    (hZU : (Z : ℝ) ≤ auxiliaryUpper B) (hY : Real.log (auxiliaryCutoff B) ≤ Y) :
    (sievePrimes Z).filter (fun p => auxiliaryCutoff B < p ∧
      p ∈ (auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) =
        largePrimeSet Z (Real.exp Y) := by
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by exact_mod_cast (by omega : 0 < auxiliaryCutoff B)
  have hPY : (auxiliaryCutoff B : ℝ) ≤ Real.exp Y := by
    simpa only [Real.exp_log hP0] using Real.exp_le_exp.mpr hY
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, _hpP, hpQ⟩ := mem_filter.mp hp
    obtain ⟨hpZ, _⟩ := mem_filter.mp hpS
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hYp := (mem_filter.mp hpQ).2
    have hxp : Real.exp Y < (p : ℝ) := by
      simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hYp
    exact mem_filter.mpr ⟨by simpa only [Nat.floor_natCast] using Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, hxp⟩
  · intro hp
    obtain ⟨hpZ, hxp⟩ := mem_filter.mp hp
    rw [Nat.floor_natCast] at hpZ
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpP : auxiliaryCutoff B < p := by exact_mod_cast (hPY.trans_lt hxp)
    have hpU : p ≤ ⌊auxiliaryUpper B⌋₊ := Nat.le_floor ((by exact_mod_cast hpZ : (p : ℝ) ≤ Z).trans hZU)
    have hlog : Y < Real.log p := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos Y) hxp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩,
      hpP, mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpU, hprime⟩, by exact_mod_cast hpP⟩, hlog⟩⟩

theorem tilt_tail_mass_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ, Real.log (auxiliaryCutoff B) ≤ Y →
      Real.log ((B : ℝ) / Y) - K ≤ tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
        ((auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := regularity_tail_prime_sum_lower hM (by linarith : 0 < c / 2)
  refine ⟨K, hK, ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [sieveCutoff_eventually hc, auxiliaryCutoff_tendsto.eventually_ge_atTop 6,
    hloglarge, eventually_gt_atTop 0] with B hcut hP hlog hB
  intro Y hY
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hZU : (sieveCutoff c B : ℝ) ≤ auxiliaryUpper B :=
    hcut.2.2.2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc4 hB0.le))
  unfold tiltPrimeReciprocalMass
  rw [tail_sieve_set B _ hP hZU hY]
  exact hbound B (sieveCutoff c B) Y hB0 (by exact_mod_cast hcut.1) hcut.2.2.1 (hlog.trans hY)

end JointDickman

end OAI
