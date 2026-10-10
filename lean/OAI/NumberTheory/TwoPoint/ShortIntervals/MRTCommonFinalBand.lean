import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalBand

namespace OAI

/-! One final original band works for both dyadic polynomials at N and
2N. The lower-endpoint margin absorbs the change in log-log scale, while
the upper endpoint remains below the smaller square-root cutoff. -/

namespace TwoPointCorrelations

open Filter Finset

lemma mrt_eventually_common_band_target :
    ∀ᶠ L : ℝ in atTop, (400*Real.log L+1)^3 ≤ Real.sqrt L := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).bound
    (show (0:ℝ)<1/800 by norm_num)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hb,hp,eventually_ge_atTop (1:ℝ)] with L hb hp hL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hh : 400*Real.log L+1 ≤ L^(1/6:ℝ) := by linarith
  calc
    _ ≤ (L^(1/6:ℝ))^3 := pow_le_pow_left₀ (by positivity) hh 3
    _ = Real.sqrt L := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le,Real.sqrt_eq_rpow]
      norm_num

lemma mrt_dyadic_log_comparison {N k : ℕ} (hN : 2 ≤ N)
    (hL : 1 ≤ Real.log (N:ℝ)) (hLL : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hNk : N ≤ k) (hk : k ≤ 2*N) :
    Real.log (N:ℝ) ≤ Real.log (k:ℝ) ∧
    Real.log (k:ℝ) ≤ 2*Real.log (N:ℝ) ∧
    Real.log (Real.log (k:ℝ)) ≤ 2*Real.log (Real.log (N:ℝ)) := by
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hk0 : 0 < (k:ℝ) := hN0.trans_le (by exact_mod_cast hNk)
  have hLN0 : 0 < Real.log (N:ℝ) := by linarith
  have hlow := Real.log_le_log hN0 (show (N:ℝ) ≤ k by exact_mod_cast hNk)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hu : Real.log (k:ℝ) ≤ 2*Real.log (N:ℝ) := by
    have hh := Real.log_le_log hk0 (show (k:ℝ) ≤ 2*(N:ℝ) by exact_mod_cast hk)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne'] at hh
    linarith
  refine ⟨hlow,hu,?_⟩
  have hh := Real.log_le_log (hLN0.trans_le hlow) hu
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hLN0.ne'] at hh
  linarith

lemma mrt_dyadic_log_error {N k : ℕ} (hN : 2 ≤ N)
    (hL : 1 ≤ Real.log (N:ℝ)) (hLL : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hNk : N ≤ k) (hk : k ≤ 2*N) :
    Real.log (Real.log (k:ℝ))/(Real.log k)^(1/100:ℝ) ≤
      2*(Real.log (Real.log (N:ℝ))/(Real.log N)^(1/100:ℝ)) := by
  obtain ⟨hlow,_,hu⟩ := mrt_dyadic_log_comparison hN hL hLL hNk hk
  have hLN0 : 0 < Real.log (N:ℝ) := by linarith
  have hlpow := Real.rpow_le_rpow hLN0.le hlow (show (0:ℝ)≤1/100 by norm_num)
  calc
    _ ≤ (2*Real.log (Real.log (N:ℝ)))/(Real.log k)^(1/100:ℝ) :=
      div_le_div_of_nonneg_right hu (by positivity)
    _ ≤ (2*Real.log (Real.log (N:ℝ)))/(Real.log N)^(1/100:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlpow
    _ = _ := by ring

lemma mrt_common_density_power {L : ℝ} (hL : 1 ≤ L) :
    Real.sqrt L ≤ L^(99/100:ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

lemma mrt_common_density_cutoff {L Q : ℝ} (hL : 1 ≤ L) (J : ℕ)
    (hup : ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt L)) :
    ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (L^(99/100:ℝ)) := by
  intro i hi
  exact (hup i hi).trans (Real.exp_le_exp.mpr (mrt_common_density_power hL))

/-- The extra-band logarithmic error is smaller than the squared
published 1/700 scale. -/
theorem mrt_log_error_published_rate :
    ∀ᶠ L : ℝ in atTop,
      Real.log L/L^(1/100:ℝ) ≤ L^(-1/350:ℝ) ∧
      Real.sqrt (Real.log L/L^(1/100:ℝ)) ≤ L^(-1/700:ℝ) := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/140 by norm_num)).bound
    (show (0:ℝ)<1 by norm_num)
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with L hb hL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _),one_mul] at hb
  have hh : Real.log L/L^(1/100:ℝ) ≤ L^(-1/350:ℝ) := by
    calc
      _ ≤ L^(1/140:ℝ)/L^(1/100:ℝ) := div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by rw [← Real.rpow_sub hL0]; norm_num
  refine ⟨hh,?_⟩
  apply (Real.sqrt_le_sqrt hh).trans_eq
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hL0.le]
  norm_num

/-- The same J satisfies the actual final-band bounds at both dyadic
cutoffs, not merely separate existential choices for the two cutoffs. -/
theorem mrt_common_final_band_geometry :
    ∀ᶠ N : ℕ in atTop, ∀ P Q : ℝ,
      1 ≤ Real.log P → 1 ≤ Real.log Q → Real.log Q ≤ Real.sqrt (Real.log N) →
      (400*Real.log (Real.log N)+1 ≤ Real.log P ∨
        Real.log (mrtBandUpper Q 2) ≤ Real.sqrt (Real.log N)) →
      ∃ J : ℕ, 1 ≤ J ∧
        Real.sqrt (Real.log N) < Real.log (mrtBandUpper Q (J+1)) ∧
        ∀ k ∈ ({N,2*N} : Finset ℕ),
          200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
          ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log k)) := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually mrt_eventually_common_band_target,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop 2] with N htarget hL hLL hN
  intro P Q hP hQ hQu hfirst
  obtain ⟨J,hJ,hlo,hnext,hup⟩ := mrt_maximal_band_lower hP hQ hQu htarget hfirst
  refine ⟨J,hJ,hnext,?_⟩
  intro k hk
  have hNk : N ≤ k := by simp only [mem_insert,mem_singleton] at hk; omega
  have hkN : k ≤ 2*N := by simp only [mem_insert,mem_singleton] at hk; omega
  obtain ⟨hloglow,_,hloghi⟩ := mrt_dyadic_log_comparison hN hL hLL hNk hkN
  refine ⟨by linarith,?_⟩
  intro i hi
  have hh : Real.log (mrtBandUpper Q i) ≤ Real.sqrt (Real.log k) :=
    (hup i hi).trans (Real.sqrt_le_sqrt hloglow)
  have he := Real.exp_le_exp.mpr hh
  rw [Real.exp_log (show 0 < mrtBandUpper Q i from Real.exp_pos _)] at he
  exact he

/-- For fixed initial P,Q the second-band alternative always holds
once N is large, yielding a common final band without extra hypotheses. -/
theorem mrt_common_final_band_fixed (P Q : ℝ)
    (hP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    ∀ᶠ N : ℕ in atTop, ∃ J : ℕ, 1 ≤ J ∧
      Real.sqrt (Real.log N) < Real.log (mrtBandUpper Q (J+1)) ∧
      ∀ k ∈ ({N,2*N} : Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log k)) := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := (Real.tendsto_sqrt_atTop.comp hlog).eventually
    (eventually_ge_atTop (max (Real.log Q) (Real.log (mrtBandUpper Q 2))))
  filter_upwards [mrt_common_final_band_geometry,hs] with N hN hs
  exact hN P Q hP hQ ((le_max_left _ _).trans hs)
    (Or.inr ((le_max_right _ _).trans hs))

end TwoPointCorrelations

end OAI
