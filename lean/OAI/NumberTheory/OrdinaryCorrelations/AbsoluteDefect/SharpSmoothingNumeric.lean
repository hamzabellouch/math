import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.GaussianL1Numeric

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

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare
open OrdinaryGaussianWindow OrdinarySharpWindow Finset Filter MeasureTheory

lemma sharp_smoothing_numeric {ε m M δ η H w I K A : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hH : 0 < H) (hw : 0 < w) (hwδ : w=δ*H)
    (hA : A ≤ 1) (hsmall : 2*δ*M+η < ε*m)
    (hK : K < η*w) (hI : w*m*I ≤ 2*A*(w^2*M)+H*K) : I < ε*H := by
  have hcoeff := mul_le_mul_of_nonneg_right hA (mul_nonneg (sq_nonneg w) hM)
  have hmain : w*m*I < 2*w^2*M+H*(η*w) := by
    have hHK := mul_lt_mul_of_pos_left hK hH
    nlinarith only [hI,hcoeff,hHK]
  have he : 2*w^2*M+H*(η*w)=w*H*(2*δ*M+η) := by rw [hwδ]; ring
  rw [he] at hmain
  have hbound := hmain.trans (mul_lt_mul_of_pos_left hsmall (mul_pos hw hH))
  apply (mul_lt_mul_iff_of_pos_left (mul_pos hw hm)).mp
  convert hbound using 1; ring

theorem dyadic_sharp_log_window_small {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ d) {ε : ℝ} (hε : 0 < ε) :
    ∃D0 : ℕ,0 < D0 ∧ ∀D : ℝ,(D0:ℝ) ≤ D → ∀ᶠ X : ℕ in atTop,
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>characterModulation f χ n/(n:ℂ)) (fun n=>Real.log n) (D/(X:ℝ)) x‖)
       <  ε*(D/(X:ℝ)) := by
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
  obtain ⟨D1,hD1,hL⟩ := dyadic_gaussian_l1_small hf hm hNP hd χ hη
  obtain ⟨D0,hD0⟩ := exists_nat_gt ((D1:ℝ)/δ)
  have hD0p : 0 < D0 := by
    have hh : (0:ℝ) < D0 := (div_pos (by exact_mod_cast hD1) hδ).trans hD0
    exact_mod_cast hh
  refine ⟨D0,hD0p,?_⟩
  intro D hD
  have hDp : 0 < D := (by exact_mod_cast hD0p : (0:ℝ) < D0).trans_le hD
  have hDδ : (D1:ℝ) ≤ δ*D := by
    have hh := (div_lt_iff₀ hδ).mp (hD0.trans_le hD)
    nlinarith only [hh]
  filter_upwards [hL (δ*D) hDδ,eventually_ge_atTop (1:ℕ)] with X hLX hXp
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
    (dyadic_coefficient_sum hf χ (show 0 < X by omega)) hsmall hLX hI

end OrdinaryChainScales

end

end OAI
