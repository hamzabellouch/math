import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalCount

namespace OAI

/-! Near-frequency energy for the literal MRT prime-band family, combining
centered cancellation with the exceptional-density bound. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_band_near_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ᶠ N : ℕ in atTop,
      ∀ (P Q : ℝ) (J : ℕ), 2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      ∀ X : ℕ, N ≤ 2 * X → X ≤ N ^ 3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (t T M : ℝ), 0 ≤ M → |t| + Real.log (2 * N : ℕ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist t) X ≤ Real.log (Real.log X) / 10 →
      (∫ u in -((Real.log N) ^ (1 / (16 : ℝ)))..((Real.log N) ^ (1 / (16 : ℝ))),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F)
          N (t + u)‖ ^ 2) ≤
        C * (Real.log P / Real.log Q + Real.exp (-M) +
          (Real.log N) ^ (-1 / (16 : ℝ))) := by
  obtain ⟨C₁, hC₁, hnear⟩ := halasz_centered_typical_energy
  obtain ⟨C₂, hC₂, hdensity⟩ := mrt_typical_density
  let C := 48 * Real.exp 1 * C₂ + C₁
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hdensity] with L hdensity
  filter_upwards [hnear, eventually_ge_atTop 2] with N hnear hN2
  have : NeZero N := ⟨by omega⟩
  intro P Q J hP hPQ hQ hmax hN X hNX hXN F hF1 hFm hFb t T M hM hT hd hsmall
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  have heq (n : ℕ) :
      mrtTypical univ (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) n ↔
        mrtTypical (Icc 1 J) V n := by
    simp [mrtTypical]
  have hp := hdensity P Q J hP hPQ hQ hmax (N + 1) N hN
  change (uniformFiniteLaw (Fin N)).probability
    (fun n => ¬mrtTypical univ
      (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) (N + 1 + n.val)) ≤ _ at hp
  have hp' : (uniformFiniteLaw (Fin N)).probability
      (fun n => ¬mrtTypical (Icc 1 J) V (N + 1 + n.val)) ≤
        C₂ * Real.log P / Real.log Q := by
    simpa only [heq] using hp
  have hcount := halasz_typical_dyadic_density_bound (Icc 1 J) V _ hp'
  have hh := hnear X hNX hXN F hF1 hFm hFb t T M hM hT hd hsmall (Icc 1 J) V
  have hR : 0 ≤ Real.log P / Real.log Q := div_nonneg
    (Real.log_nonneg (by linarith)) (by linarith)
  have hB : 0 ≤ Real.exp (-M) + (Real.log N) ^ (-1 / (16 : ℝ)) := by positivity
  have hA : 0 ≤ 48 * Real.exp 1 * C₂ := by positivity
  calc
    _ ≤ 48 * Real.exp 1 *
          (C₂ * Real.log P / Real.log Q) +
        C₁ * (Real.exp (-M) + (Real.log N) ^ (-1 / (16 : ℝ))) := by
      apply hh.trans
      have hs := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ 48 * Real.exp 1)
      simpa only [mul_div_assoc, add_comm] using add_le_add_right hs
        (C₁ * (Real.exp (-M) + (Real.log N) ^ (-1 / (16 : ℝ))))
    _ = (48 * Real.exp 1 * C₂) * (Real.log P / Real.log Q) +
        C₁ * (Real.exp (-M) + (Real.log N) ^ (-1 / (16 : ℝ))) := by ring
    _ ≤ _ := by
      dsimp [C]
      nlinarith [mul_nonneg hA hB, mul_nonneg hC₁.le hR]

end TwoPointCorrelations

end OAI
