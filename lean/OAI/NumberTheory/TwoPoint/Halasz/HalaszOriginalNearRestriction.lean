import OAI.NumberTheory.TwoPoint.Halasz.HalaszOriginalNearEnergy

namespace OAI

/-! Near-center energy restricted to the lower half of the frequency
range, where the original published height controls all required twists. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

lemma halasz_center_window_quarter_room :
    ∀ᶠ N : ℕ in atTop,
      Real.log (2*N:ℕ)^8+(Real.log N)^(1/16:ℝ) ≤ (N:ℝ)/4 := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := (isLittleO_pow_exp_pos_mul_atTop 8 (b := 1) (by norm_num)).bound
    (show (0:ℝ)<1/2048 by norm_num)
  filter_upwards [hlog.eventually hb,hlog.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop 2] with N hb hLN hN
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hLN0 : 0 ≤ Real.log (N:ℝ) := by linarith
  have hL2 : 0 ≤ Real.log (2*N:ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤2*N by omega))
  have hup : Real.log (2*N:ℕ) ≤ 2*Real.log (N:ℝ) := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne']
    linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
  have hp := pow_le_pow_left₀ hL2 hup 8
  norm_num [mul_pow] at hp
  have hpow : Real.log (N:ℝ) ≤ Real.log (N:ℝ)^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hLN (show 1≤8 by norm_num)
  have hr := Real.rpow_le_self_of_one_le hLN (show (1/16:ℝ)≤1 by norm_num)
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤Real.log (N:ℝ)^8),
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_log hN0] at hb
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at ⊢
  nlinarith

theorem halasz_sharp_near_original_restriction : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 1 ≤ J →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ X : ℕ, N ≤ 2*X → X ≤ N^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ τ M : ℝ, 0 ≤ M →
      (∀ v:ℝ, |v| ≤ (N:ℝ)/2 → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      ∀ E : Set ℝ, E ⊆ Set.Ioc (-((N:ℝ)/4)) ((N:ℝ)/4) →
      E ⊆ Set.Ioc (τ-(Real.log N)^(1/16:ℝ)) (τ+(Real.log N)^(1/16:ℝ)) →
      (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
        C*((Real.log P/Real.log Q)^2+Real.exp (-M)+(Real.log N)^(-1/32:ℝ)) := by
  obtain ⟨C,hC,hnear⟩ := halasz_sharp_near_original_scale
  refine ⟨C,hC,?_⟩
  filter_upwards [hnear,halasz_center_window_quarter_room,eventually_ge_atTop 2] with N hnear hroom hN2
  intro P Q J hP hPQ hQ hJ hmax X hNX hXN F hF1 hFm hFb τ M hM hd hsmall E hEN hEt
  by_cases hE : E.Nonempty
  · obtain ⟨t,ht⟩ := hE
    have hN := hEN ht
    have hT := hEt ht
    have hτ : |τ| ≤ (N:ℝ)/4+(Real.log N)^(1/16:ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [hN.1,hN.2,hT.1,hT.2]
    have hroom' : |τ|+Real.log (2*N:ℕ)^8 ≤ (N:ℝ)/2 := by linarith
    exact halasz_restricted_near_energy _ N τ ((Real.log N)^(1/16:ℝ)) _
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))) _)
      (hnear P Q J hP hPQ hQ hJ hmax X hNX hXN F hF1 hFm hFb τ ((N:ℝ)/2) M hM hroom' hd hsmall) E hEt
  · rw [Set.not_nonempty_iff_eq_empty.mp hE]
    simp only [MeasureTheory.setIntegral_empty]
    positivity

end TwoPointCorrelations

end OAI
