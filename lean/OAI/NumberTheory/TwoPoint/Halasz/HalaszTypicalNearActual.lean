import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalPrefix
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNearBound
import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandDensity
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNearBandSum

namespace OAI

/-! The actual typical-band near energy retains exponential saving,
with no discarded-density term in the amplitude. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_typical_near_actual : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ J →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ (X : ℕ) (τ T M : ℝ), X ≤ N^3 → 0 ≤ M → |τ|+Real.log (2*N:ℕ)^8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤ Real.log (Real.log (2*N:ℕ))/10 →
      (∫ u in -((Real.log N)^(1/16:ℝ))..((Real.log N)^(1/16:ℝ)),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N (τ+u)‖^2) ≤
        C*(Real.exp (-4*M/5)+(Real.log N)^(-1/32:ℝ)) := by
  obtain ⟨C₀,hC₀,hcenter⟩ := halasz_typical_centered_prefix
  let D := 36*(halaszPrimePowerLogConstant+1)*Real.exp 8
  refine ⟨100*Real.pi*C₀^2+100*D^2,by positivity,?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hcenter,mrt_band_near_renormalization,hl,eventually_ge_atTop 2]
    with N hcenter hnear hL hN
  intro P Q J hP hPQ hlogP hJ hmax F hF1 hFm hFb X τ T M hX hM hT hd hsmall
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let B := halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J) V F) τ
  have hQ : 1 ≤ Real.log Q := hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  have hpr : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, p.Prime := fun _ _ _ hp => mrtPrimeBand_prime hp
  have hupper : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log N)) := by
    intro j hj p hp
    exact ((mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp).2).trans (hmax j hj)
  have hc := hcenter X hX F hF1 hFm hFb τ T M hM hT hd (Icc 1 J) V hpr
    (halasz_actual_bands_disjoint P Q J hP hPQ hlogP) hupper
  have hD : 0 ≤ D := by dsimp [D,halaszPrimePowerLogConstant]; positivity
  have hn : ∀ u ∈ Set.Icc (-((Real.log N)^(1/16:ℝ))) ((Real.log N)^(1/16:ℝ)),
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B u k-(halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*
        halaszPhaseMean B 0 k‖ ≤ (D*(Real.log N)^(-3/50:ℝ))*k := by
    intro u hu k hk
    exact hnear P Q J hQ hJ hmax F hF1 (fun a b ha hb _ => hFm a b ha hb) hFb
      τ hsmall u (abs_le.mpr hu) k hk
  have hh := halasz_typical_near_bound B (by omega) C₀ D (Real.log N) M hC₀.le hD hL hc hn
  simpa only [B,halasz_twisted_dyadic] using hh

end TwoPointCorrelations

end OAI
