import OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitRepulsion
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDistanceCutoff

namespace OAI

/-! Moderate twist repulsion at the smaller cofactor cutoff. -/
namespace TwoPointCorrelations

open Filter

theorem halasz_moderate_cutoff (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), OneBounded F → ∀ v τ : ℝ,
      1/2 ≤ |v-τ| → |v-τ| ≤ (Real.log X)^20 →
      squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
  obtain ⟨K₀,hK₀,hcut⟩ := halasz_distance_cutoff_loss
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp halasz_moderate_distance_unit
  have hll := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (500*(K+K₀)))
  filter_upwards [eventually_ge_atTop n₀,eventually_ge_atTop 2,hll]
    with n hn hn2 hlln
  intro X hnX hX F hF v τ hlo hhi hmin
  have hrep := hn₀ X (hn.trans hnX) F hF ∅ v τ hlo hhi hmin
  have he : mrtMissingCoefficient F ∅ = F := by
    funext k
    simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
  rw [he] at hrep
  have hlogn : 0 < Real.log (n:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hlog : Real.log (n:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0<n by omega)) (by exact_mod_cast hnX)
  have hllmono := Real.log_le_log hlogn hlog
  have hc := hcut F hF n X hn2 hnX hX v
  dsimp only [Function.comp_def] at hlln
  linarith

end TwoPointCorrelations

end OAI
