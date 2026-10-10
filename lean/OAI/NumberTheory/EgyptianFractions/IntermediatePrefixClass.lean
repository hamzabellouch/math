import OAI.NumberTheory.EgyptianFractions.IntermediatePrimeClass
import OAI.NumberTheory.EgyptianFractions.LargePrimeDivisors
import OAI.NumberTheory.EgyptianFractions.PrimePrefixSize
import OAI.NumberTheory.EgyptianFractions.RankinAdmissibility

namespace OAI
open scoped BigOperators Topology
open Filter

namespace Problem337.DivisorMoment

/-- Prime-factor prefix data defining one intermediate dyadic band. This does
not assume either a divisor-count estimate or a lower bound on the prefix. -/
def IntermediatePrefixWitness (n d p : ℕ) (Y v t : ℝ) : Prop :=
  d ∣ n ∧ (d : ℝ) ≤ Real.sqrt Y ∧ Real.sqrt Y < (d : ℝ) * p ∧ p.Prime ∧
  Real.log (p : ℝ) < v ^ (15 / 16 : ℝ) ∧
  t ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * t ∧
  (∀ q : ℕ, q.Prime → q ∣ d → q ≤ p) ∧
  (∀ q ∈ (n / d).primeFactorsList, p ≤ q)

/-- The actual intermediate prefix class: the lower-prefix and pointwise
moment hypotheses of the Rankin class bound are derived from factorization
data and the crossing of the square-root cutoff. -/
theorem intermediate_selected_prefix_moment_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (X Y v t W : ℝ) (H : Finset ℕ),
      1 < X → Real.log X = v → 1 ≤ Y → v / 2 ≤ Real.log Y →
      1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      v ^ (15 / 16 : ℝ) ≤ v / 20 → v ≤ W →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ H, ∃ d p : ℕ, IntermediatePrefixWitness (N + h) d p Y v t) →
      (∑ h ∈ H, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤ 2 * Y *
        Real.exp (r * ((1 + Real.log (W / v)) * v / t) -
          (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_prime_class_sqrt_bound r
  refine ⟨C, hC, ?_⟩
  intro N X Y v t W H hX hXv hY hYlog ht htv hβ hsmall hvW hH hNW hpfx
  apply hbound N Y v t (r * ((1 + Real.log (W / v)) * v / t)) H
    (fun h => (truncatedDivisorCount X (N + h) : ℝ) ^ r)
    hY ht htv hβ hH
  intro h hh
  obtain ⟨d, p, hdvd, hdY, hcross, hp, hplog, htp, hpt, hdfactors, hqfactors⟩ := hpfx h hh
  have hnpos : 0 < N + h := by
    have hh1 := (Finset.mem_Icc.mp (hH hh)).1
    omega
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hplarge : Real.exp (v / 5) < (d : ℝ) :=
    PrimePrefixSize.exp_prefix_lower hdposR hppos (by linarith)
      hYlog hcross hplog hsmall
  have hpcap : (p : ℝ) ≤ Real.exp (2 * t) := by
    calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hppos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hpt
  have hlowp : Real.exp t ≤ (p : ℝ) := by
    calc
      Real.exp t ≤ Real.exp (Real.log (p : ℝ)) := Real.exp_le_exp.mpr htp
      _ = _ := Real.exp_log hppos
  refine ⟨d, hdvd, hdY, hplarge.le, ?_, ?_⟩
  · intro q hq hqd
    exact (Nat.cast_le.mpr (hdfactors q hq hqd)).trans hpcap
  · have hmoment := truncatedDivisorCount_prefix_moment_bound X (Real.exp t) W r
      (Nat.ne_of_gt hnpos) hdvd hX (Real.one_lt_exp_iff.mpr (by linarith))
      (by simpa only [hXv] using hvW) (hNW h hh) hr (by
        intro q hq
        exact hlowp.trans (Nat.cast_le.mpr (hqfactors q hq)))
    simpa only [Real.log_exp, hXv, mul_comm] using hmoment

/-- Uniform scale version with both the Rankin admissibility and the lower
prefix size discharged. This is ready for a finite dyadic union. -/
theorem eventually_intermediate_selected_prefix_moment_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      ∀ (N : ℕ) (X Y v t W : ℝ) (H : Finset ℕ),
      1 < X → Real.log X = v → 1 ≤ Y → v / 2 ≤ Real.log Y →
      S / (2 * Real.log S) ≤ v → v ≤ S ^ 2 →
      1 ≤ t → t ≤ v → 4 * Real.log S ≤ t → v ≤ W →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ H, ∃ d p : ℕ, IntermediatePrefixWitness (N + h) d p Y v t) →
      (∑ h ∈ H, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤ 2 * Y *
        Real.exp (r * ((1 + Real.log (W / v)) * v / t) -
          (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_selected_prefix_moment_bound r hr
  obtain ⟨V, hV⟩ := eventually_atTop.mp PrimePrefixSize.eventually_fifteen_sixteenths_small
  refine ⟨C, hC, ?_⟩
  filter_upwards [PrimePrefixSize.eventually_uniform_lower_scale V,
    eventually_gt_atTop (1 : ℝ)] with S hS hSone
  intro N X Y v t W H hX hXv hY hYlog hvlow hvhigh ht htv htlow hvW hH hNW hpfx
  exact hbound N X Y v t W H hX hXv hY hYlog ht htv
    (Problem337.rankin_band_exponent_admissible S v t hSone ht htv hvhigh htlow)
    (hV v (hS v hvlow)) hvW hH hNW hpfx

end Problem337.DivisorMoment

end OAI
