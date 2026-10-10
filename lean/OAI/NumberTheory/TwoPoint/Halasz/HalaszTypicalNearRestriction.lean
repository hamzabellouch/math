import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalNearActual
import OAI.NumberTheory.TwoPoint.Halasz.HalaszOriginalNearRestriction

namespace OAI

/-! Restricted typical energy at the original pretentious cutoff. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_typical_near_original_restriction : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ J →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ X : ℕ, N ≤ 2*X → X ≤ N^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → (∀ a b, 0<a → 0<b → F (a*b)=F a*F b) → OneBounded F →
      ∀ τ M : ℝ, 0 ≤ M →
      (∀ v:ℝ, |v| ≤ (N:ℝ)/2 → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      ∀ E : Set ℝ, E ⊆ Set.Ioc (-((N:ℝ)/4)) ((N:ℝ)/4) →
      E ⊆ Set.Ioc (τ-(Real.log N)^(1/16:ℝ)) (τ+(Real.log N)^(1/16:ℝ)) →
      (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
        C*(Real.exp (-4*M/5)+(Real.log N)^(-1/32:ℝ)) := by
  obtain ⟨C,hC,hnear⟩ := halasz_typical_near_actual
  refine ⟨C,hC,?_⟩
  filter_upwards [hnear,halasz_center_window_quarter_room,eventually_ge_atTop 2] with N hnear hroom hN2
  intro P Q J hP hPQ hlogP hJ hmax X _hNX hXN F hF1 hFm hFb τ M hM hd hsmall E hEN hEt
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
      (hnear P Q J hP hPQ hlogP hJ hmax F hF1 hFm hFb X τ ((N:ℝ)/2) M hXN hM hroom' hd hsmall) E hEt
  · rw [Set.not_nonempty_iff_eq_empty.mp hE]
    simp only [MeasureTheory.setIntegral_empty]
    positivity

end TwoPointCorrelations

end OAI
