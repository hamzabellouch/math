import OAI.NumberTheory.EgyptianFractions.IntermediatePrefixClass
import OAI.NumberTheory.EgyptianFractions.DivisorClasses
import OAI.NumberTheory.EgyptianFractions.DivisorBandDecay

namespace OAI
open Filter
open scoped Topology BigOperators

namespace Problem337.DivisorMoment
attribute [local instance] Classical.propDecidable

/-- The final uniform intermediate-band budget for the actual canonical
prime-factor class. All arithmetic, counting, and exponent estimates are
proved here; no class-moment estimate remains as an assumption. -/
theorem eventually_intermediate_band_budget (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (v Y : ℝ) (N j : ℕ),
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      (N : ℝ) ≤ Real.exp (D * S) →
      4 * Real.log S * 2 ^ j ≤ v ^ (15 / 16 : ℝ) →
      (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun h => DivisorClasses.BandClass (N + h) S v Y j),
        (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤ 2 * Y := by
  classical
  obtain ⟨C, hC, hclass⟩ := eventually_intermediate_selected_prefix_moment_bound r hr
  have hdec := eventually_uniform_intermediate_band_decay (D + 1) r C
    (by linarith) hr hC.le
  filter_upwards [hclass, hdec, PrimePrefixSize.eventually_uniform_lower_scale 1,
    eventually_ge_atTop (max D (Real.exp 1)), eventually_ge_atTop (1 : ℝ)]
    with S hclass hdec hscale hS hSone
  intro v Y N j hvlow hvhigh hYlow hYhigh hN hj
  let t : ℝ := 4 * Real.log S * 2 ^ j
  let H : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun h => DivisorClasses.BandClass (N + h) S v Y j)
  have hvone : 1 ≤ v := hscale v hvlow
  have hvpos : 0 < v := by linarith
  have hSpos : 0 < S := by linarith
  have hSD : D ≤ S := (le_max_left _ _).trans hS
  have hSexp : Real.exp 1 ≤ S := (le_max_right _ _).trans hS
  have hlogS : 1 ≤ Real.log S := (Real.le_log_iff_exp_le hSpos).mpr hSexp
  have htlow : 4 * Real.log S ≤ t := by
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    dsimp [t]
    nlinarith
  have htone : 1 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have htv : t ≤ v := by
    calc
      t ≤ v ^ (15 / 16 : ℝ) := hj
      _ ≤ v := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hvone (by norm_num : (15 / 16 : ℝ) ≤ 1)
  have hvSsq : v ≤ S ^ 2 := by nlinarith
  have hYone : 1 ≤ Y := (Real.one_le_exp (by linarith : 0 ≤ v / 2)).trans hYlow
  have hYpos : 0 < Y := by linarith
  have hYlog : v / 2 ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hYlow
  have hvW : v ≤ (D + 1) * S := by nlinarith
  have hH : H ⊆ Finset.Icc 1 ⌊Y⌋₊ := Finset.filter_subset _ _
  have hNW : ∀ h ∈ H, Real.log ((N + h : ℕ) : ℝ) ≤ (D + 1) * S := by
    intro h hh
    have hhI := Finset.mem_Icc.mp (hH hh)
    have hnhpos : (0 : ℝ) < ((N + h : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < N + h by omega)
    have hhY : (h : ℝ) ≤ Y :=
      (Nat.cast_le.mpr hhI.2).trans (Nat.floor_le hYpos.le)
    have hhexp : (h : ℝ) ≤ Real.exp (D * S) :=
      hhY.trans (hYhigh.trans (Real.exp_le_exp.mpr hvhigh))
    apply (Real.log_le_iff_le_exp hnhpos).mpr
    calc
      ((N + h : ℕ) : ℝ) ≤ 2 * Real.exp (D * S) := by push_cast; linarith
      _ ≤ Real.exp S * Real.exp (D * S) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp S]
      _ = Real.exp ((D + 1) * S) := by rw [← Real.exp_add]; congr 1; ring
  have hpfx : ∀ h ∈ H, ∃ d p : ℕ,
      IntermediatePrefixWitness (N + h) d p Y v t := by
    intro h hh
    obtain ⟨d, p, hpref, hpsmall, hband⟩ := (Finset.mem_filter.mp hh).2
    obtain ⟨hdpos, hp, hdvd, hdY, hcross, hpd, hdprime, hqprime⟩ := hpref
    refine ⟨d, p, hdvd, hdY, ?_, hp, hpsmall, hband.1, ?_, hdprime, ?_⟩
    · simpa only [Nat.cast_mul] using hcross
    · have hhi := hband.2
      dsimp [t]
      rw [pow_succ] at hhi
      nlinarith
    · intro q hq
      exact hqprime q (Nat.prime_of_mem_primeFactorsList hq)
        (Nat.dvd_of_mem_primeFactorsList hq)
  have hbound := hclass N (Real.exp v) Y v t ((D + 1) * S) H
    (Real.one_lt_exp_iff.mpr hvpos) (Real.log_exp v) hYone hYlog
    hvlow hvSsq htone htv htlow hvW hH hNW hpfx
  have hdecay := hdec v t hvlow htpos hj
  have hQ : 1 ≤ v / t := (one_le_div htpos).mpr htv
  have hQlog : 0 ≤ (v / t) * Real.log (v / t) :=
    mul_nonneg (by linarith) (Real.log_nonneg hQ)
  have harg : r * ((1 + Real.log ((D + 1) * S / v)) * v / t) -
      (v / t) * Real.log (v / t) / 50 +
      C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤ 0 := by
    have heq : r * ((1 + Real.log ((D + 1) * S / v)) * v / t) =
        r * (1 + Real.log ((D + 1) * S / v)) * (v / t) := by ring
    rw [heq]
    linarith
  change (∑ h ∈ H, (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤ _
  exact hbound.trans (by
    have he := Real.exp_le_one_iff.mpr harg
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * Y))

end Problem337.DivisorMoment

end OAI
