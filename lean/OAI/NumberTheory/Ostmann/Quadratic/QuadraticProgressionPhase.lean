import OAI.NumberTheory.Ostmann.ZeroDensity.PositiveResidueProgression
import OAI.NumberTheory.Ostmann.Characters.SchwartzWeightVariation
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedQuadraticLift

namespace OAI

/-! # The actual progression has quadratic coefficient s*v*q*theta -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem quadratic_progression_weight_argument (q s v a j : ℕ) (R : ℝ)
    (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    (s : ℝ) * v * ((a + q * j : ℕ) : ℝ) ^ 2 / (R * q) =
      (((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  rw [div_pow, Real.sq_sqrt (by positivity)]
  push_cast
  field_simp
  ring

theorem quadratic_progression_phase (q s v a j : ℕ) (θ : ℝ) (hq : 0 < q) :
    realAdditivePhase (θ * s * v * ((a + q * j : ℕ) : ℝ) ^ 2 / q) =
      realAdditivePhase (θ * s * v * (a : ℝ) ^ 2 / q) *
        realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * a) j := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [realQuadraticPhase, ← realAdditivePhase_add]
  congr 1
  push_cast
  field_simp
  ring

theorem quadraticResidueWave_progression (q s v a j : ℕ) (θ R : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    quadraticResidueWave (q := q) θ Φ R s v (a + q * j) =
      realAdditivePhase (θ * s * v * (a : ℝ) ^ 2 / q) *
        (Φ ((((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * a) j) := by
  rw [quadraticResidueWave, quadratic_progression_weight_argument q s v a j R hq hs hv hR,
    quadratic_progression_phase q s v a j θ hq]
  ring

theorem quadratic_progression_sum_norm (q s v a N : ℕ) (θ R : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    ‖∑ j ∈ Finset.range N, quadraticResidueWave (q := q) θ Φ R s v (a + q * j)‖ =
      ‖∑ j ∈ Finset.range N,
        Φ ((((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * a) j‖ := by
  simp_rw [quadraticResidueWave_progression q s v a _ θ R Φ hq hs hv hR]
  rw [← Finset.mul_sum, norm_mul, norm_realAdditivePhase, one_mul]

theorem quadratic_progression_weight_variation (q s v a N : ℕ) (R C : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (hq : 0 < q) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R)
    (hN : (N : ℝ) ≤ C * Real.sqrt (R / ((s : ℝ) * v * q))) :
    discreteVariation (fun j : ℕ =>
      Φ ((((j : ℝ) + (a : ℝ) / q) / Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2)) N ≤
      SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) +
        SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * C := by
  apply quadratic_schwartz_rescaled_variation
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    exact Real.sqrt_pos.mpr (by positivity)
  · exact hN

end Ostmann

end OAI
