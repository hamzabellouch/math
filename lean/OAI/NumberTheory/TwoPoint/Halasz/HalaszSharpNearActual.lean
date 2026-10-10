import OAI.NumberTheory.TwoPoint.Halasz.HalaszSharpNearEnergy
import OAI.NumberTheory.TwoPoint.Halasz.HalaszNearActualScale
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNearBandSum
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNearPrefix

namespace OAI

/-! Sharp near-frequency energy for the literal original MRT bands,
with every pretentious-distance condition at the original cutoff. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_sharp_near_actual_scale : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 1 ≤ J →
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
  intro P Q J hP hPQ hQ hJ hmax F hF1 hFm hFb τ M hM hτ hd hsmall
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let B := halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J) V F) τ
  have hcube : 2*N ≤ N^3 := by
    have hs : 2 ≤ N^2 := by nlinarith
    calc
      2*N ≤ N^2*N := Nat.mul_le_mul_right N hs
      _ = N^3 := by ring
  have hc := hcenter (2*N) (by omega) hcube F hF1 hFm hFb τ (2*N) M hM hτ hd
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

theorem halasz_sharp_near_restricted_actual_scale : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 1 ≤ J →
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
        C*((Real.log P/Real.log Q)^2+Real.exp (-M)+(Real.log N)^(-1/32:ℝ)) := by
  obtain ⟨C,hC,hnear⟩ := halasz_sharp_near_actual_scale
  refine ⟨C,hC,?_⟩
  filter_upwards [hnear,halasz_center_window_room,eventually_ge_atTop 2] with N hnear hroom hN2
  intro P Q J hP hPQ hQ hJ hmax F hF1 hFm hFb τ M hM hd hsmall E hEN hEt
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
      (hnear P Q J hP hPQ hQ hJ hmax F hF1 hFm hFb τ M hM hroom' hd hsmall) E hEt
  · rw [Set.not_nonempty_iff_eq_empty.mp hE]
    simp only [MeasureTheory.setIntegral_empty]
    positivity

end TwoPointCorrelations

end OAI
