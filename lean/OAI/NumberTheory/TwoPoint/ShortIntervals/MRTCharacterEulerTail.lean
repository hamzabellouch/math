import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLSeries
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPrimeTail

namespace OAI

/-! Absolute truncation of the character Euler product at sigma=1+1/log X.
Together with the horizontal shift this identifies the finite prime sum
with the logarithm of the actual L-series, up to an absolute error. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical LSeries.notation

lemma mrt_character_shifted_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {eps : ℝ} (heps : 0≤eps) {p : ℕ} (hp : p.Prime) :
    ‖(characterTwist χ t p/(p:ℂ))*(Real.exp (-eps*Real.log (p:ℝ)):ℂ)‖≤1/2 := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hn : ‖characterTwist χ t p/(p:ℂ)‖≤1/2 := by
    rw [norm_div,Complex.norm_natCast]
    exact (div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p)
      (Nat.cast_nonneg p)).trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have he : Real.exp (-eps*Real.log (p:ℝ))≤1 := by
    apply Real.exp_le_one_iff.mpr
    have hl := Real.log_nonneg (show (1:ℝ)≤p by linarith)
    nlinarith
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_of_le_one_right (norm_nonneg _) he).trans hn

lemma mrt_character_shifted_log_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {eps : ℝ} (heps : 0≤eps) (S : Finset ℕ) (hS : ∀p∈S,p.Prime) :
    Real.log ‖mrtCharacterShiftedEuler χ t eps S‖ =
      ∑ p ∈ S, Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-eps*Real.log (p:ℝ)):ℂ))⁻¹‖ := by
  rw [mrtCharacterShiftedEuler,norm_prod]
  apply Real.log_prod
  intro p hp
  apply norm_ne_zero_iff.mpr
  apply inv_ne_zero
  intro he
  have hz := mrt_character_shifted_norm χ t heps (hS p hp)
  rw [show (characterTwist χ t p/(p:ℂ))*
    (Real.exp (-eps*Real.log (p:ℝ)):ℂ)=1 from (sub_eq_zero.mp he).symm,norm_one] at hz
  norm_num at hz

lemma mrt_character_shifted_log_local {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {eps : ℝ} (heps : 0≤eps) {p : ℕ} (hp : p.Prime) :
    |Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
      (Real.exp (-eps*Real.log (p:ℝ)):ℂ))⁻¹‖| ≤
        2*Real.exp (-eps*Real.log (p:ℝ))/(p:ℝ) := by
  have hh := mrt_local_euler_log_lipschitz (mrt_character_shifted_norm χ t heps hp)
    (show ‖(0:ℂ)‖≤1/2 by norm_num)
  simp only [sub_zero,inv_one,norm_one,Real.log_one] at hh
  have hb : ‖characterTwist χ t p/(p:ℂ)‖≤1/(p:ℝ) := by
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p) (Nat.cast_nonneg p)
  have hn : ‖(characterTwist χ t p/(p:ℂ))*
      (Real.exp (-eps*Real.log (p:ℝ)):ℂ)‖≤
      Real.exp (-eps*Real.log (p:ℝ))/(p:ℝ) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    convert mul_le_mul_of_nonneg_right hb (Real.exp_pos (-eps*Real.log (p:ℝ))).le using 1
    ring
  apply hh.trans
  calc
    _ ≤ 2*(Real.exp (-eps*Real.log (p:ℝ))/(p:ℝ)) :=
      mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = _ := by ring

lemma mrt_character_shifted_finite_tail {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {X Y : ℕ} (hX : 1≤Real.log (X:ℝ)) (hXY : X≤Y) :
    |Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo Y)‖-
      Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo X)‖| ≤
        8+8*halaszMertensConstant := by
  have heps : 0≤1/Real.log (X:ℝ) := by positivity
  have hsub : primesUpTo X⊆primesUpTo Y := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hp).trans_le (by omega)),hprime⟩
  let S := primesUpTo Y \ primesUpTo X
  have hS : ∀p∈S,p.Prime ∧ X<p := by
    intro p hp
    obtain ⟨hy,hx⟩ := mem_sdiff.mp hp
    have hprime := (mem_filter.mp hy).2
    refine ⟨hprime,?_⟩
    by_contra hh
    exact hx (mem_filter.mpr ⟨mem_range.mpr (by omega),hprime⟩)
  rw [mrt_character_shifted_log_sum χ t heps (primesUpTo Y) (fun p hp => (mem_filter.mp hp).2),
    mrt_character_shifted_log_sum χ t heps (primesUpTo X) (fun p hp => (mem_filter.mp hp).2),
    ← sum_sdiff_eq_sub hsub]
  calc
    _ ≤ ∑ p ∈ S, |Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-(1/Real.log (X:ℝ))*Real.log (p:ℝ)):ℂ))⁻¹‖| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, 2*Real.exp (-(1/Real.log (X:ℝ))*Real.log (p:ℝ))/(p:ℝ) :=
      sum_le_sum (fun p hp => mrt_character_shifted_log_local χ t heps (hS p hp).1)
    _ = 2*∑ p ∈ S, Real.exp (-Real.log (p:ℝ)/Real.log (X:ℝ))/(p:ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      rw [show -(1/Real.log (X:ℝ))*Real.log (p:ℝ)=
        -Real.log (p:ℝ)/Real.log (X:ℝ) by ring]
      ring
    _ ≤ 8+8*halaszMertensConstant := by
      have hh := mrt_character_prime_tail_bound hX S hS
      nlinarith

theorem mrt_character_LSeries_truncation {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {X : ℕ} (hX : 1≤Real.log (X:ℝ)) :
    |Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
      Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo X)‖| ≤
        8+8*halaszMertensConstant := by
  have heps : 0<1/Real.log (X:ℝ) := by positivity
  have hs : 1<(1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I).re := by
    simp only [Complex.sub_re,Complex.add_re,Complex.one_re,Complex.ofReal_re,
      Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
    linarith
  have hn := χ.LSeries_ne_zero_of_one_lt_re hs
  have ht := mrt_character_shifted_euler_limit χ t heps
  have hlog := (Real.continuousAt_log (norm_ne_zero_iff.mpr hn)).tendsto.comp ht.norm
  apply le_of_tendsto ((hlog.sub tendsto_const_nhds).abs)
  filter_upwards [eventually_ge_atTop X] with Y hXY
  exact mrt_character_shifted_finite_tail χ t hX hXY

theorem mrt_character_euler_LSeries_comparison {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {X : ℕ} (hX : 1≤Real.log (X:ℝ)) :
    |Real.log ‖mrtCharacterPrimeEuler χ t (primesUpTo X)‖-
      Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖| ≤
        10+10*halaszMertensConstant := by
  have hshift := mrt_character_euler_logarithmic_shift χ t hX (primesUpTo X) Subset.rfl
  have htail := mrt_character_LSeries_truncation χ t hX
  have hh := abs_sub_le (Real.log ‖mrtCharacterPrimeEuler χ t (primesUpTo X)‖)
    (Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) (primesUpTo X)‖)
    (Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖)
  rw [abs_sub_comm] at htail
  linarith

theorem mrt_character_prime_tail_LSeries_ratio {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {Y X : ℕ}
    (hY : 1≤Real.log (Y:ℝ)) (hX : 1≤Real.log (X:ℝ)) (hYX : Y≤X) :
    |(∑ p ∈ primesUpTo X \ primesUpTo Y, characterTwist χ t p/(p:ℂ)).re-
      (Real.log ‖L ↗χ (1+(1/Real.log (X:ℝ):ℝ)-(t:ℂ)*Complex.I)‖-
        Real.log ‖L ↗χ (1+(1/Real.log (Y:ℝ):ℝ)-(t:ℂ)*Complex.I)‖)| ≤
        24+20*halaszMertensConstant := by
  have hsub : primesUpTo Y⊆primesUpTo X := by
    intro p hp
    obtain ⟨hp,hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hp).trans_le (by omega)),hprime⟩
  rw [sum_sdiff_eq_sub hsub,Complex.sub_re]
  have hEX := abs_le.mp (mrt_character_euler_log_error χ t X (primesUpTo X) Subset.rfl)
  have hEY := abs_le.mp (mrt_character_euler_log_error χ t Y (primesUpTo Y) Subset.rfl)
  have hLX := abs_le.mp (mrt_character_euler_LSeries_comparison χ t hX)
  have hLY := abs_le.mp (mrt_character_euler_LSeries_comparison χ t hY)
  apply abs_le.mpr
  constructor <;> linarith [hEX.1,hEX.2,hEY.1,hEY.2,hLX.1,hLX.2,hLY.1,hLY.2]

end TwoPointCorrelations

end OAI
