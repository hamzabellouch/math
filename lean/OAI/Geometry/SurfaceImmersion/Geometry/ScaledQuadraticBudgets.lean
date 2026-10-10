import OAI.Geometry.SurfaceImmersion.Geometry.DisjointJetBounds

namespace OAI

/-! C1 smallness and a radius-independent C2 budget for the actual scaled
quadratic corrections. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets

theorem scaled_quadratic_C1_C2_budgets (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (B : SecondTensor), ‖B‖ ≤ K →
      ∀ (p : Plane) (r : ℝ), 0 < r → r ≤ 1 →
        WeightedEstimates.WeightedBound univ 1 1 (D*r) (scaledQuadraticCutoff B p r) ∧
        WeightedEstimates.WeightedBound univ 1 2 D (scaledQuadraticCutoff B p r) := by
  obtain ⟨C,hC,hb⟩ := uniform_scaled_quadratic_bounds
  let D := C*K
  have hD : 0 ≤ D := mul_nonneg hC hK
  refine ⟨D,hD,?_⟩
  intro B hB p r hr hr1
  have hCK : C*‖B‖ ≤ D := mul_le_mul_of_nonneg_left hB hC
  have hbound (j : ℕ) (hj : j ≤ 2) (x : Plane) :
      r^j * ‖iteratedFDeriv ℝ j (scaledQuadraticCutoff B p r) x‖ ≤ D*r^2 := by
    exact (hb B p r hr j hj x).trans (mul_le_mul_of_nonneg_right hCK (sq_nonneg r))
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hrr : r^2 ≤ r := by nlinarith
  constructor
  · intro j hj x hx
    rw [iteratedFDerivWithin_univ]
    simp only [one_pow,one_mul]
    have hh := hbound j (by omega) x
    interval_cases j
    · simp only [pow_zero,one_mul] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hrr hD)
    · simp only [pow_one] at hh
      nlinarith
  · intro j hj x hx
    rw [iteratedFDerivWithin_univ]
    simp only [one_pow,one_mul]
    have hh := hbound j hj x
    interval_cases j
    · simp only [pow_zero,one_mul] at hh
      exact hh.trans (by nlinarith [mul_nonneg hD (by nlinarith : 0 ≤ 1-r^2)])
    · simp only [pow_one] at hh
      nlinarith [mul_nonneg hD (by linarith : 0 ≤ 1-r)]
    · nlinarith

end ClosedSurfaceR4.SphericalJets

end

end OAI
