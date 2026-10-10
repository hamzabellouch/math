import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSampleScale

namespace OAI

/-! The additional large-prime interval used after the last ordinary
band. A factor two in its lower logarithm absorbs bin rounding. -/

namespace TwoPointCorrelations

open Filter Finset
open scoped Classical

noncomputable def mrtExtraPrimeLower (L : ℝ) : ℝ :=
  Real.exp (2*L^(79/80:ℝ))

noncomputable def mrtExtraPrimeUpper (L : ℝ) : ℝ :=
  Real.exp (L/Real.log L)

noncomputable def mrtExtraPrimeResolution (L : ℝ) : ℝ := L^(1/80:ℝ)

theorem mrt_extra_band_geometry :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ mrtExtraPrimeResolution L ∧
      Real.exp (Real.sqrt L) < mrtExtraPrimeLower L ∧
      mrtExtraPrimeLower L ≤ mrtExtraPrimeUpper L ∧
      mrtExtraPrimeUpper L ≤ Real.exp (L/1000) ∧
      ∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L)
        (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
      1 < mrtPrimeLogLower (mrtExtraPrimeResolution L) k ∧
      L^(79/80:ℝ) ≤ Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) ∧
      Real.log (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) ≤ L := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).bound
    (show (0:ℝ)<1/2 by norm_num)
  have hres := (tendsto_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hb,hres,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))]
    with L hb hres hL hLL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg hlogL.le,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hsmall : 2*Real.log L ≤ L^(1/80:ℝ) := by linarith
  have hpow : 1 ≤ L^(79/80:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hmul : L^(79/80:ℝ)*L^(1/80:ℝ)=L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hPQ : mrtExtraPrimeLower L ≤ mrtExtraPrimeUpper L := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hlogL).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le (79/80))
    rw [hmul] at hh
    nlinarith
  have hsep : Real.exp (Real.sqrt L) < mrtExtraPrimeLower L := by
    apply Real.exp_lt_exp.mpr
    have hh : Real.sqrt L ≤ L^(79/80:ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    linarith
  have hupper : mrtExtraPrimeUpper L ≤ Real.exp (L/1000) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hL0.le (by norm_num) hLL
  refine ⟨hres,hsep,hPQ,hupper,?_⟩
  intro k hk
  let Y := mrtPrimeLogLower (mrtExtraPrimeResolution L) k
  have hYlow : L^(79/80:ℝ) ≤ Real.log Y := by
    have hh := mrt_log_bin_lower_endpoint (show 1 ≤ mrtExtraPrimeResolution L by
      change 1 ≤ L^(1/80:ℝ)
      linarith)
      (Real.exp_pos _) (mem_Icc.mp hk).1
    have hh' := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hh
    rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp] at hh'
    simp only [Real.log_exp] at hh'
    change -1+2*L^(79/80:ℝ) ≤ Real.log Y at hh'
    linarith
  have hY : 1 < Y := by
    change 1 < Real.exp ((k:ℝ)/mrtExtraPrimeResolution L)
    apply Real.one_lt_exp_iff.mpr
    have hh : 0 < Real.log Y := by linarith
    simpa only [Y,mrtPrimeLogLower,Real.log_exp] using hh
  have hQ1 : 1 ≤ mrtExtraPrimeUpper L := Real.one_le_exp (by positivity)
  have hYhi := mrt_prime_log_lower_le_upper (show 0 < mrtExtraPrimeResolution L by
    change 0 < L^(1/80:ℝ)
    linarith)
    hQ1 (mem_Icc.mp hk).2
  have hl : Real.log Y ≤ L/Real.log L := by
    simpa only [mrtExtraPrimeUpper,Real.log_exp] using
      Real.log_le_log (show 0 < Y by linarith) hYhi
  exact ⟨hY,hYlow,hl.trans (div_le_self hL0.le (by linarith))⟩

/-- The additional interval is disjoint from every original prime set
under the proved maximal-band upper cutoff. -/
theorem mrt_extra_band_disjoint :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
      Disjoint S (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) := by
  filter_upwards [mrt_extra_band_geometry] with L hL
  intro S hS
  apply disjoint_left.mpr
  intro p hp hq
  have hh := (mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hq).1
  have hs := hS p hp
  have hsep : Real.exp (Real.sqrt L) < Real.exp (2*L^(79/80:ℝ)) := hL.2.1
  linarith

end TwoPointCorrelations

end OAI
