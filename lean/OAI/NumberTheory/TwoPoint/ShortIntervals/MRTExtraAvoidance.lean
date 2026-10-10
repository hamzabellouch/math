import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSieveBounds

namespace OAI

/-! Actual integer-interval density of missing the additional prime band.
Both sieve errors are paid, with no independence assumption on integers. -/

namespace TwoPointCorrelations

open Filter Finset

theorem mrt_extra_prime_avoidance : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (A N : ℕ) [NeZero N], Real.exp L ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids
          (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) (A+j.val)) ≤
        C*Real.log L/L^(1/80:ℝ) := by
  obtain ⟨C,hC,hband⟩ := mrt_missing_band_probability
  refine ⟨2*C+2,by positivity,?_⟩
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).bound
    (show (0:ℝ)<1/8 by norm_num)
  filter_upwards [mrt_extra_band_geometry,mrt_extra_prime_mass,hb,
    eventually_ge_atTop (120:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (100:ℝ))]
    with L hg hm hb hL hLL
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLgt : 1 < L := by linarith
  have hlog : 0 < Real.log L := by linarith
  rw [Real.norm_eq_abs,abs_of_pos hlog,Real.norm_eq_abs,Real.rpow_one,
    abs_of_pos hL0] at hb
  have hsmall : Real.log L/5+3 ≤ L/20 := by linarith
  intro A N _ hN
  let r := ⌈Real.log L/10⌉₊
  have hrlo : Real.log L/10 ≤ (r:ℝ) := Nat.le_ceil _
  have hrhi : (r:ℝ) < Real.log L/10+1 := Nat.ceil_lt_add_one (by positivity)
  have horder : Real.log L/5 ≤ ((2*r+1:ℕ):ℝ) := by push_cast; linarith
  have horder' : ((2*r+1:ℕ):ℝ) ≤ Real.log L/5+3 := by push_cast; linarith
  have htail := mrt_extra_sieve_tail hL1
    (show (∑ p ∈ mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
      1/(p:ℝ)) ≤ Real.log L/50 by linarith [hm.2]) horder
  have hboundary := mrt_extra_sieve_boundary N r hL1 hLL hsmall
    (show 0 ≤ mrtExtraPrimeUpper L from (Real.exp_pos _).le)
    (show mrtExtraPrimeUpper L ≤ Real.exp (L/Real.log L) from le_rfl)
    (Nat.cast_nonneg (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)).card)
    (mrt_prime_band_card_le (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
      (Real.exp_pos _).le) hN horder'
  have hpower : L^(-3/50:ℝ) ≤ Real.log L/L^(1/80:ℝ) := by
    calc
      _ ≤ L^(-1/80:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = 1/L^(1/80:ℝ) := by
        have he : (-1/80:ℝ) = -(1/80:ℝ) := by ring
        rw [he,Real.rpow_neg hL0.le]
        simp only [one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hexp : Real.exp (-L/4) ≤ L^(-3/50:ℝ) := by
    rw [Real.rpow_def_of_pos hL0]
    apply Real.exp_le_exp.mpr
    linarith [Real.log_le_sub_one_of_pos hL0]
  have hh := hband (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L) hm.1 hg.2.2.1 A N r
  rw [mul_div_assoc,mrt_extra_prime_ratio hLgt] at hh
  calc
    _ ≤ C*(2*Real.log L/L^(1/80:ℝ))+2*(Real.log L/L^(1/80:ℝ)) := by
      linarith [htail.trans hpower,hboundary.trans (hexp.trans hpower)]
    _ = _ := by ring

end TwoPointCorrelations

end OAI
