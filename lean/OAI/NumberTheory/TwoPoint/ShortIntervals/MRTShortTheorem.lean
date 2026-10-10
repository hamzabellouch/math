import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFullWorkingMean
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortTrivialCases
import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortNormalization

namespace OAI

/-! Corrected MRT Theorem 1.7 at every natural scale, reduced only to the
sparse-prime and high-prime estimates used in the analytic argument. -/
namespace TwoPointCorrelations

open Filter

theorem mrt_short_exponential_of_prime_estimates
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    MRTShortExponentialInput := by
  obtain ⟨C,hC,W₀,X₀,hfull⟩ := mrt_full_actual_working_mean hprime hhigh
  obtain ⟨W₁,hrem⟩ := eventually_atTop.mp major_arc_working_length_remainder
  obtain ⟨W₂,hpower⟩ := eventually_atTop.mp (major_arc_working_length_power 1)
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₁,hX₁⟩ := eventually_atTop.mp
    ((hlog.eventually major_arc_parameter_rate).and
      ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and (eventually_ge_atTop X₀)))
  let B := max (Real.exp 5) (max W₀ (max W₁ W₂))
  obtain ⟨C₀,hC₀,htrivial⟩ := mrt_short_trivial_cases B X₁
  refine ⟨C₀+2*C+21,by positivity,?_⟩
  intro X H hH hHX F hFm hFb M hd α
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let E := Real.exp (-M/20)+mrtShortError X H
  have hE : 0 ≤ E := add_nonneg (Real.exp_pos _).le (mrt_short_error_nonneg hH hHX)
  have hsmall (hcase : W ≤ B ∨ X ≤ X₁) :
      shortExponentialIntegral F X H α ≤ (C₀+2*C+21)*(H:ℝ)*X*E := by
    have hs := htrivial X H hH hHX F hFb M hcase α
    apply hs.trans
    have hc : C₀ ≤ C₀+2*C+21 := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg H))
        (Nat.cast_nonneg X)) hE
  by_cases hwsmall : W ≤ B
  · exact hsmall (Or.inl hwsmall)
  by_cases hxsmall : X ≤ X₁
  · exact hsmall (Or.inr hxsmall)
  have hBW : B ≤ W := (le_of_not_ge hwsmall)
  have hW₀ : W₀ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hBW)
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hBW))
  have hW₂ : W₂ ≤ W := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hBW))
  have heW : Real.exp 5 ≤ W := (le_max_left _ _).trans hBW
  have hM : 0 ≤ M := by
    have hWe : W ≤ Real.exp (M/3) := (min_le_right _ _).trans (min_le_right _ _)
    have hMe := Real.exp_le_exp.mp (heW.trans hWe)
    linarith
  obtain ⟨hLH,hLL⟩ := mrt_large_parameter_logs hH heW
  obtain ⟨hrate,hLX,hXX₀⟩ := hX₁ X (le_of_not_ge hxsmall)
  obtain ⟨hW,hWH,_,_⟩ := major_arc_parameter_bounds hLX hLH hM
  have hW0 : 0 < W := by linarith
  have hWh : W ≤ (h:ℝ) := by
    simpa only [pow_one] using hpower W hW₂ H (by omega) hLH hWH
  have hh : 0 < h := by exact_mod_cast hW0.trans_le hWh
  have hhH : h ≤ H := major_arc_working_length_le H W
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0<H by omega)
  rcases hFm.one_zero_or_one with hzero | hone
  · rw [shortExponentialIntegral_of_one_zero hFm hzero]
    positivity
  have hmean := hfull X H hXX₀ hH hHX hLH hLL M hM hW₀
  have htail : W^(-1/4:ℝ) ≤ 21*E := by
    have hk := hrate H M hLH hLL hM
    rw [mul_div_assoc] at hk
    have hw : W^(-1/4:ℝ) ≤ majorArcWorkingError W := by
      apply (Real.rpow_le_rpow_of_exponent_le hW (show (-1/4:ℝ)≤-1/5 by norm_num)).trans
      exact le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW])
    have hs : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have hl : 0 ≤ (Real.log X)^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    dsimp only [E,mrtShortError]
    linarith only [hk,hw,hs,hl]
  have hlarge : shortExponentialIntegral F X H α ≤ (2*C+21)*(X:ℝ)*H*E := by
    rcases hrem W hW₁ H with heq | hratio
    · have hm := hmean X le_rfl (by change X+h ≤ 2*X; omega) F hone hFm hFb hd α
      change h=H at heq
      change shortExponentialIntegral F X h α ≤ C*(X:ℝ)*h*E at hm
      rw [heq] at hm
      have hconstant : C ≤ 2*C+21 := by linarith
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant
          (Nat.cast_nonneg X)) (Nat.cast_nonneg H)) hE)
    · let Y := X+H-h
      have hXY : X ≤ Y := by dsimp [Y]; omega
      have hY : Y+h ≤ 2*X := by dsimp [Y]; omega
      have hm := hmean Y hXY hY F hone hFm hFb hd α
      have hcount : ((H/h:ℕ):ℝ)*(h:ℝ) ≤ H := by exact_mod_cast Nat.div_mul_le_self H h
      have hYreal : (Y:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show Y≤2*X by omega)
      have hmain : ((H/h:ℕ):ℝ)*shortExponentialIntegral F Y h α ≤ 2*C*X*H*E := by
        calc
          _ ≤ ((H/h:ℕ):ℝ)*(C*(Y:ℝ)*h*E) :=
            mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
          _ = (C*(Y:ℝ)*E)*(((H/h:ℕ):ℝ)*h) := by ring
          _ ≤ (C*(2*X)*E)*(H:ℝ) := by gcongr
          _ = _ := by ring
      have hboundary : (X:ℝ)*h ≤ 21*(X:ℝ)*H*E := by
        have hb : (h:ℝ) ≤ (21*E)*H := (div_le_iff₀ hH0).mp (hratio.trans htail)
        have hs := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg X)
        convert hs using 1; ring
      have hs := mrt_short_integral_subdivision_sharp F hFb X H h hh hhH α
      change shortExponentialIntegral F X H α ≤
        ((H/h:ℕ):ℝ)*shortExponentialIntegral F Y h α+(X:ℝ)*h at hs
      apply hs.trans
      have ht := add_le_add hmain hboundary
      convert ht using 1; ring
  apply hlarge.trans
  have hc : 2*C+21 ≤ C₀+2*C+21 := by linarith
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg X))
      (Nat.cast_nonneg H)) hE
  convert hh using 1; ring

end TwoPointCorrelations

end OAI
