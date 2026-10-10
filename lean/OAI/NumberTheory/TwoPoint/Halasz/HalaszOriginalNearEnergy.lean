import OAI.NumberTheory.TwoPoint.Halasz.HalaszSharpNearActual

namespace OAI

/-! Keep the original pretentious cutoff and height in the sharp
near-center bound, independently of the dyadic polynomial's cutoff. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_sharp_near_original_scale : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 1 ≤ J →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ X : ℕ, N ≤ 2*X → X ≤ N^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ τ T M : ℝ, 0 ≤ M → |τ|+Real.log (2*N:ℕ)^8 ≤ T →
      (∀ v:ℝ, |v| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      (∫ u in -((Real.log N)^(1/16:ℝ))..((Real.log N)^(1/16:ℝ)),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F)
          N (τ+u)‖^2) ≤
        C*((Real.log P/Real.log Q)^2+Real.exp (-M)+(Real.log N)^(-1/32:ℝ)) := by
  obtain ⟨C₁,hC₁,hcenter⟩ := halasz_centered_prefix
  obtain ⟨C₂,hC₂,hprefix⟩ := mrt_typical_centered_prefix_density
  let D := 36*(halaszPrimePowerLogConstant+1)*Real.exp 8
  refine ⟨600*Real.pi*C₁^2+300*Real.pi*C₂^2+100*D^2,by positivity,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hcenter,hprefix,mrt_band_near_renormalization,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop 2]
    with N hcenter hprefix hnear hL hN2
  intro P Q J hP hPQ hQ hJ hmax X hNX hXN F hF1 hFm hFb τ T M hM hτ hd hsmall
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let B := halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J) V F) τ
  have hc := hcenter X hNX hXN F hF1 hFm hFb τ T M hM hτ hd
  have hp := hprefix P Q J hP hPQ hQ hmax F hFb τ
  have hR : 0 ≤ Real.log P/Real.log Q :=
    div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hD : 0 ≤ D := by dsimp [D,halaszPrimePowerLogConstant]; positivity
  have hn : ∀ u ∈ Set.Icc (-((Real.log N)^(1/16:ℝ))) ((Real.log N)^(1/16:ℝ)),
      ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B u k -
        (halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*halaszPhaseMean B 0 k‖ ≤
          (D*(Real.log N)^(-3/50:ℝ))*k := by
    intro u hu k hk
    exact hnear P Q J hQ hJ hmax F hF1 hFm hFb τ hsmall u (abs_le.mpr hu) k hk
  have hh := halasz_sharp_near_energy B (halaszTwistedFunction F τ) (by omega)
    C₁ C₂ D (Real.log N) M (Real.log P/Real.log Q) hC₁.le hC₂.le hD hL hR hc hp hn
  simpa only [B,halasz_twisted_dyadic] using hh

end TwoPointCorrelations

end OAI
