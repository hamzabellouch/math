import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SharpSmoothingNumeric
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicGaussianL1Power

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryMellinModulus
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare
open OrdinaryGaussianWindow OrdinarySharpWindow OrdinaryChainScales Finset Filter MeasureTheory

theorem dyadic_sharp_log_power_logarithmic :
    ∃ A c k : ℕ, ∀ m : ℕ,
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {d : ℕ}, 0<d → ∀χ : DirichletCharacter ℂ d,
      ∀D : ℝ,
      ((16*(2*(m+k)+2+c+1)*2^(2^(29*(2*(m+k)+2+3)+A)):ℕ):ℝ) /
        ((1/2:ℝ)^m*bumpMass/(8*(bumpMoment+1)))≤D →
      ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
      < (1/2:ℝ)^m*(D/(X:ℝ)) := by
  obtain ⟨A,c,hA⟩ := dyadic_gaussian_l1_power_logarithmic
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
    (div_pos bumpMass_pos (by norm_num : (0:ℝ)<4)) (by norm_num : (1/2:ℝ)<1)
  refine ⟨A,c,k,?_⟩
  intro m f hf hm hNP d hd χ
  let ε : ℝ := (1/2:ℝ)^m
  have hε : 0<ε := by dsimp [ε]; positivity
  let δ := ε*bumpMass/(8*(bumpMoment+1))
  let η := ε*bumpMass/4
  have hM := bumpMoment_nonneg
  have hm0 := bumpMass_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hsmall : 2*δ*bumpMoment+η < ε*bumpMass := by
    have he : δ*(8*(bumpMoment+1))=ε*bumpMass :=
      div_mul_cancel₀ _ (by positivity)
    dsimp [η]
    nlinarith only [he,hδ,mul_pos hε hm0]
  let D1 : ℕ := 16*(2*(m+k)+2+c+1)*2^(2^(29*(2*(m+k)+2+3)+A))
  have hD1 : 0<D1 := by dsimp [D1]; positivity
  intro D hD
  have hDδ : (D1:ℝ)≤δ*D := by
    change (D1:ℝ)/δ≤D at hD
    have hh := (div_le_iff₀ hδ).mp hD
    calc (D1:ℝ) ≤ D*δ := hh
         _ = δ*D := mul_comm _ _
  have hDp : 0<D := by
    have hprod : 0<δ*D := (by exact_mod_cast hD1 : (0:ℝ)<D1).trans_le hDδ
    exact (mul_pos_iff_of_pos_left hδ).mp hprod
  have hL := hA (m+k) hf hm hNP hd χ (δ*D) hDδ
  have hη' : (1/2:ℝ)^(m+k)≤η := by
    rw [pow_add]
    have hh := mul_le_mul_of_nonneg_left hk.le (show 0≤ε by positivity)
    dsimp [η,ε] at *
    linarith only [hh]
  filter_upwards [hL,eventually_ge_atTop (1:ℕ)] with X hLX hXp
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let H := D/(X:ℝ)
  let w := δ*D/(X:ℝ)
  have hH : 0 < H := div_pos hDp hXr
  have hw : 0 < w := div_pos (mul_pos hδ hDp) hXr
  have he : w=δ*H := by dsimp [w,H]; ring
  have hI := sharp_l1_le_kernel (Ioc X (2*X))
    (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n)
    (dilateKernel_integrable hw) (fun z=>bump_nonneg _)
    (dilateKernel_moment_integrable hw) hH.le
  rw [dilateKernel_mass hw,dilateKernel_moment hw,kernelWindow_dilate] at hI
  exact sharp_smoothing_numeric hm0 hM hH hw he
    (dyadic_coefficient_sum hf χ (show 0 < X by omega)) hsmall
      (hLX.trans_le (mul_le_mul_of_nonneg_right hη' hw.le)) hI

end OrdinaryMellinModulus

end

end OAI
