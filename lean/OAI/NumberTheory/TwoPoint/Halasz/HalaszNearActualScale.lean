import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandNearEnergy
import OAI.NumberTheory.TwoPoint.Halasz.HalaszNearRestriction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Near-frequency energy with the single actual scale L=log N.
The density and mean-value thresholds are taken independently before
this diagonal specialization. -/
namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_band_near_actual_scale : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ τ M : ℝ, 0 ≤ M → |τ|+Real.log (2*N:ℕ)^8 ≤ 2*N →
      (∀ v:ℝ, |v| ≤ 2*N → M ≤ squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      (∫ u in -((Real.log N)^(1/16:ℝ))..((Real.log N)^(1/16:ℝ)),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F)
          N (τ+u)‖^2) ≤
        C*(Real.log P/Real.log Q+Real.exp (-M)+(Real.log N)^(-1/16:ℝ)) := by
  obtain ⟨C₁,hC₁,hnear⟩ := halasz_centered_typical_energy
  obtain ⟨C₂,hC₂,hdensity⟩ := mrt_typical_density
  refine ⟨48*Real.exp 1*C₂+C₁,by positivity,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnear,hlog.eventually hdensity,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop 2]
    with N hnear hdensity hlogN hN2
  intro P Q J hP hPQ hQ hmax F hF1 hFm hFb τ M hM hτ hd hsmall
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have : NeZero N := ⟨by omega⟩
  have hs : Real.sqrt (Real.log N) ≤ (Real.log N)^(99/100:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlogN (by norm_num)
  have hscale : (1/2:ℝ)*Real.exp ((Real.log N)^(199/200:ℝ)) ≤ N := by
    have hp := Real.rpow_le_self_of_one_le hlogN (show (199/200:ℝ)≤1 by norm_num)
    have he := Real.exp_le_exp.mpr hp
    rw [Real.exp_log hN0] at he
    nlinarith [Real.exp_pos ((Real.log N)^(199/200:ℝ))]
  have heq (n:ℕ) :
      mrtTypical univ (fun j:{j:ℕ // j∈(Icc 1 J:Finset ℕ)} => V j) n ↔
        mrtTypical (Icc 1 J) V n := by simp [mrtTypical]
  have hp := hdensity P Q J hP hPQ hQ
    (fun j hj => (hmax j hj).trans (Real.exp_le_exp.mpr hs)) (N+1) N hscale
  change (uniformFiniteLaw (Fin N)).probability
    (fun n => ¬mrtTypical univ
      (fun j:{j:ℕ // j∈(Icc 1 J:Finset ℕ)} => V j) (N+1+n.val)) ≤ _ at hp
  have hp' : (uniformFiniteLaw (Fin N)).probability
      (fun n => ¬mrtTypical (Icc 1 J) V (N+1+n.val)) ≤ C₂*Real.log P/Real.log Q := by
    simpa only [heq] using hp
  have hcount := halasz_typical_dyadic_density_bound (Icc 1 J) V _ hp'
  have hcube : 2*N ≤ N^3 := by
    have hs : 2 ≤ N^2 := by nlinarith
    calc
      2*N ≤ N^2*N := Nat.mul_le_mul_right N hs
      _ = N^3 := by ring
  have hh := hnear (2*N) (by omega) hcube F hF1 hFm hFb τ (2*N) M hM hτ hd hsmall
    (Icc 1 J) V
  have hR : 0 ≤ Real.log P/Real.log Q := div_nonneg
    (Real.log_nonneg (by linarith)) (by linarith)
  have hB : 0 ≤ Real.exp (-M)+(Real.log N)^(-1/16:ℝ) := by positivity
  have hA : 0 ≤ 48*Real.exp 1*C₂ := by positivity
  calc
    _ ≤ 48*Real.exp 1*(C₂*Real.log P/Real.log Q)+
        C₁*(Real.exp (-M)+(Real.log N)^(-1/16:ℝ)) := by
      apply hh.trans
      have hs' := mul_le_mul_of_nonneg_left hcount (show (0:ℝ)≤48*Real.exp 1 by positivity)
      simpa only [mul_div_assoc,add_comm] using add_le_add_right hs'
        (C₁*(Real.exp (-M)+(Real.log N)^(-1/16:ℝ)))
    _ = (48*Real.exp 1*C₂)*(Real.log P/Real.log Q)+
        C₁*(Real.exp (-M)+(Real.log N)^(-1/16:ℝ)) := by ring
    _ ≤ _ := by nlinarith [mul_nonneg hA hB,mul_nonneg hC₁.le hR]

lemma halasz_center_window_room :
    ∀ᶠ N : ℕ in atTop,
      Real.log (2*N:ℕ)^8+(Real.log N)^(1/16:ℝ) ≤ N := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := (isLittleO_pow_exp_pos_mul_atTop 8 (b := 1) (by norm_num)).bound
    (show (0:ℝ)<1/512 by norm_num)
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

theorem halasz_near_restricted_actual_scale : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ τ M : ℝ, 0 ≤ M →
      (∀ v:ℝ, |v| ≤ 2*N → M ≤ squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      ∀ E : Set ℝ, E ⊆ Set.Ioc (-(N:ℝ)) N →
      E ⊆ Set.Ioc (τ-(Real.log N)^(1/16:ℝ)) (τ+(Real.log N)^(1/16:ℝ)) →
      (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
        C*(Real.log P/Real.log Q+Real.exp (-M)+(Real.log N)^(-1/16:ℝ)) := by
  obtain ⟨C,hC,hnear⟩ := halasz_band_near_actual_scale
  refine ⟨C,hC,?_⟩
  filter_upwards [hnear,halasz_center_window_room,eventually_ge_atTop 2] with N hnear hroom hN2
  intro P Q J hP hPQ hQ hmax F hF1 hFm hFb τ M hM hd hsmall E hEN hEt
  by_cases hE : E.Nonempty
  · obtain ⟨t,ht⟩ := hE
    have hN := hEN ht
    have hT := hEt ht
    have hτ : |τ| ≤ (N:ℝ)+(Real.log N)^(1/16:ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [hN.1,hN.2,hT.1,hT.2]
    have hroom' : |τ|+Real.log (2*N:ℕ)^8 ≤ 2*N := by linarith
    exact halasz_restricted_near_energy _ N τ ((Real.log N)^(1/16:ℝ)) _
      (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))) _)
      (hnear P Q J hP hPQ hQ hmax F hF1 hFm hFb τ M hM hroom' hd hsmall) E hEt
  · rw [Set.not_nonempty_iff_eq_empty.mp hE]
    simp only [MeasureTheory.setIntegral_empty]
    have hlogP : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
    positivity

end TwoPointCorrelations

end OAI
