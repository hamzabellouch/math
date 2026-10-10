import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalBandBudget

namespace OAI

/-! A single final band for every quotient dyadic above the square-root
cutoff. The band is chosen before the quotient and the dyadic origin. -/

namespace TwoPointCorrelations

open Filter Finset

lemma mrt_quotient_band_target :
    ∀ᶠ L : ℝ in atTop, (400*Real.log L+1)^3 ≤ Real.sqrt L/2 := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).bound
    (show (0:ℝ)<1/1600 by norm_num)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/6 by norm_num)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hb,hp,eventually_ge_atTop (1:ℝ)] with L hb hp hL
  have hL0 : 0 < L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
  have hh : 400*Real.log L+1 ≤ L^(1/6:ℝ)/2 := by linarith
  calc
    _ ≤ (L^(1/6:ℝ)/2)^3 := pow_le_pow_left₀ (by positivity) hh 3
    _ = Real.sqrt L/8 := by
      rw [div_pow,← Real.rpow_natCast,← Real.rpow_mul hL0.le,Real.sqrt_eq_rpow]
      norm_num
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg L]

lemma mrt_quotient_band_alternative :
    ∀ᶠ L : ℝ in atTop, ∀ P Q : ℝ, 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      400*Real.log L+1 ≤ Real.log P ∨
        Real.log (mrtBandUpper Q 2) ≤ Real.sqrt L/2 := by
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<249/500 by norm_num)).eventually
    (eventually_ge_atTop (2048:ℝ))
  filter_upwards [hp,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with L hp hL hlogL
  have hL0 : 0 < L := by linarith
  intro P Q hQ hbudget
  by_cases hfirst : 400*Real.log L+1 ≤ Real.log P
  · exact Or.inl hfirst
  right
  have hnot : Real.log P < 400*Real.log L+1 := lt_of_not_ge hfirst
  have hsmall : Real.log (Real.log Q) ≤ Real.log L/1000 := by linarith
  have hQ0 : 0 < Real.log Q := by linarith
  have hq : Real.log Q ≤ L^(1/1000:ℝ) := by
    calc
      _ = Real.exp (Real.log (Real.log Q)) := (Real.exp_log hQ0).symm
      _ ≤ Real.exp (Real.log L/1000) := Real.exp_le_exp.mpr hsmall
      _ = _ := by rw [Real.rpow_def_of_pos hL0]; congr 1; ring
  have hu : Real.log (mrtBandUpper Q 2) ≤ 1024*L^(1/500:ℝ) := by
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log Q) hq 2
    have he : (L^(1/1000:ℝ))^2=L^(1/500:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      norm_num
    rw [he] at hs
    have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤1024)
    have heq : Real.log (mrtBandUpper Q 2)=1024*(Real.log Q)^2 := by
      norm_num [mrtBandUpper]
    rw [heq]
    exact hm
  apply hu.trans
  calc
    1024*L^(1/500:ℝ) ≤ (L^(249/500:ℝ)/2)*L^(1/500:ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hL0.le _)
    _ = Real.sqrt L/2 := by
      rw [div_mul_eq_mul_div,← Real.rpow_add hL0,Real.sqrt_eq_rpow]
      norm_num

lemma mrt_quotient_dyadic_log {X n : ℕ} (hX : 2 ≤ X)
    (hn : ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n) :
    Real.log (X:ℝ)/2 ≤ Real.log (n:ℝ) ∧
      Real.sqrt (Real.log (X:ℝ))/2 ≤ Real.sqrt (Real.log (n:ℝ)) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hnr : Real.sqrt (X:ℝ) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn0 : 0 < (n:ℝ) := (Real.sqrt_pos.2 hX0).trans_le hnr
  have hsq : (X:ℝ) ≤ (n:ℝ)^2 := by
    nlinarith [Real.sq_sqrt hX0.le,Real.sqrt_nonneg (X:ℝ)]
  have hl := Real.log_le_log hX0 hsq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hLX : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤X by omega))
  have hln : 0 ≤ Real.log (n:ℝ) := by linarith
  refine ⟨by linarith,?_⟩
  nlinarith [Real.sq_sqrt hLX,Real.sq_sqrt hln,
    Real.sqrt_nonneg (Real.log (X:ℝ)),Real.sqrt_nonneg (Real.log (n:ℝ))]

theorem mrt_quotient_common_final_band :
    ∀ᶠ X : ℕ in atTop, ∀ P Q : ℝ,
      1 ≤ Real.log P → 1 ≤ Real.log Q →
      Real.log Q ≤ Real.sqrt (Real.log X)/2 →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      ∃ J : ℕ, 1 ≤ J ∧
        200*Real.log (Real.log (4*(X:ℝ)))+1 ≤ Real.log (mrtBandLower P Q J) ∧
        Real.sqrt (Real.log X)/2 < Real.log (mrtBandUpper Q (J+1)) ∧
        (∀ i ∈ Icc 1 J, Real.log (mrtBandUpper Q i) ≤ Real.sqrt (Real.log X)/2) ∧
        ∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 4*X →
          200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
          ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log n)) := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually mrt_quotient_band_target,
    hlog.eventually mrt_quotient_band_alternative,
    hlog.eventually (eventually_ge_atTop (2:ℝ)),
    (Real.tendsto_log_atTop.comp hlog).eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (4:ℕ)] with X htarget halt hL hLL hX
  change 1 ≤ Real.log (Real.log (X:ℝ)) at hLL
  intro P Q hP hQ hQU hbudget
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hLX : 0 < Real.log (X:ℝ) := by linarith
  have hlog4 : Real.log 4 ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hdouble : Real.log (4*(X:ℝ)) ≤ 2*Real.log (X:ℝ) := by
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hX0.ne']
    linarith
  have hll4 : Real.log (Real.log (4*(X:ℝ))) ≤ 2*Real.log (Real.log (X:ℝ)) := by
    have hpositive : 0 < Real.log (4*(X:ℝ)) := by
      rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hX0.ne']
      linarith [Real.log_nonneg (show (1:ℝ)≤4 by norm_num)]
    have hh := Real.log_le_log hpositive hdouble
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hLX.ne'] at hh
    linarith
  obtain ⟨J,hJ,hlo,hnext,hup⟩ := mrt_maximal_band_lower hP hQ hQU htarget
    (halt P Q hQ hbudget)
  have hlow : 200*Real.log (Real.log (4*(X:ℝ)))+1 ≤ Real.log (mrtBandLower P Q J) := by
    linarith
  refine ⟨J,hJ,hlow,hnext,hup,?_⟩
  intro n hn hnX
  obtain ⟨hln,hroot⟩ := mrt_quotient_dyadic_log (by omega : 2≤X) hn
  have hn0 : 0 < Real.log (n:ℝ) := by linarith
  have hnpos : 0 < (n:ℝ) :=
    (Real.sqrt_pos.2 hX0).trans_le ((Nat.le_ceil _).trans (by exact_mod_cast hn))
  have hl4 : Real.log (n:ℝ) ≤ Real.log (4*(X:ℝ)) :=
    Real.log_le_log hnpos (by exact_mod_cast hnX)
  refine ⟨(by linarith [Real.log_le_log hn0 hl4]),?_⟩
  intro i hi
  have he := Real.exp_le_exp.mpr ((hup i hi).trans hroot)
  rwa [Real.exp_log (show 0 < mrtBandUpper Q i from Real.exp_pos _)] at he

end TwoPointCorrelations

end OAI
