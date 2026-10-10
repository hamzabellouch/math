import OAI.NumberTheory.TwoPoint.Halasz.HalaszModeratePhase

namespace OAI

/-! Moderate-frequency repulsion outside a fixed unit interval. -/
namespace TwoPointCorrelations

open Filter

theorem halasz_moderate_distance_unit :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ) (t t₁ : ℝ),
      1/2 ≤ |t - t₁| →
      |t - t₁| ≤ (Real.log N) ^ 20 →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N →
      (31 / 500 : ℝ) * Real.log (Real.log N) ≤
        squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (Real.log N)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hlog)
  have hll := (Real.tendsto_log_atTop.comp hlog).eventually
    (eventually_ge_atTop (1000 : ℝ))
  filter_upwards [hroot.eventually halasz_moderate_masked_distance,
    hlog.eventually (eventually_ge_atTop (4 : ℝ)), hll] with N hN hl hllN
  dsimp only [Function.comp_def] at hllN
  intro F hF Q t t₁ htlo hthi hmin
  have hl0 : 0 ≤ Real.log N := by linarith
  have hs : Real.sqrt (Real.sqrt (Real.log N)) ^ 2 = Real.sqrt (Real.log N) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hfour : Real.sqrt (Real.sqrt (Real.log N)) ^ 4 = Real.log N := by
    calc
      _ = (Real.sqrt (Real.sqrt (Real.log N)) ^ 2) ^ 2 := by ring
      _ = Real.log N := by rw [hs, Real.sq_sqrt hl0]
  have h80 : Real.sqrt (Real.sqrt (Real.log N)) ^ 80 = (Real.log N) ^ 20 := by
    calc
      _ = (Real.sqrt (Real.sqrt (Real.log N)) ^ 4) ^ 20 := by rw [← pow_mul]
      _ = _ := by rw [hfour]
  have hs2 : 2 ≤ Real.sqrt (Real.log N) := by
    have hsq := Real.sq_sqrt hl0
    have hn := Real.sqrt_nonneg (Real.log N)
    nlinarith
  have ht : 1 ≤ |t - t₁| * Real.sqrt (Real.log N) := by nlinarith
  have hh := hN F hF Q N t t₁ hfour.symm
    (by simpa only [hs] using ht) (by simpa only [h80] using hthi) hmin
  linarith

end TwoPointCorrelations

end OAI
