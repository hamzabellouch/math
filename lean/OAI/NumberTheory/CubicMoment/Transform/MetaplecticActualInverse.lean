import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedPolynomial

namespace OAI

/-! Exact inverse completion for the original angular, norm-twisted
smooth Gauss sum. All cube-divisor sums are finite by the actual support
of the weight, and the rescaled completed length is retained literally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticAngularSmoothSum (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U t : ℝ) : ℂ :=
  ∑' u : PrimaryArgument,
    (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U)

lemma metaplecticAngularSmoothSum_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticAngularSmoothSum r ℓ W U t =
      ∑ u ∈ primaryElementBall F,
        W (norm u/U)*(gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)) := by
  let S := (primaryElementBall F).subtype primary
  have he : metaplecticAngularSmoothSum r ℓ W U t =
      ∑ u ∈ S, (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U) := by
    apply tsum_eq_sum
    intro u hu
    have hnorm : F < norm u := by
      by_contra hn
      exact hu (Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨u.property,le_of_not_gt hn⟩))
    rw [hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hnorm)),mul_zero]
  rw [he]
  dsimp only [S]
  rw [Finset.sum_subtype_of_mem
    (fun u : Eisenstein => (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u))*W (norm u/U))
    (fun _ hu => (mem_primaryElementBall.mp hu).1)]
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- Equation (angular-inversion), with the height-dependent inverse
weight and the original compactly supported sum on its left. -/
theorem metaplectic_angular_actual_inverse
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticAngularSmoothSum r ℓ W U t =
      ∑ c ∈ primaryElementBall F,
        ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c)*
          metaplecticHeightCompleted r ℓ W (U/norm c^3) t := by
  rw [metaplecticAngularSmoothSum_finite r ℓ W hU hBF hW t,
    metaplectic_gauss_primary_inverse r ℓ t F (fun x => W (x/U))]
  have hcut : ∀ x : ℝ, F < x → W (x/U) = 0 := by
    intro x hx
    exact hW _ ((lt_div_iff₀ hU).mpr (hBF.trans_lt hx))
  let g : Eisenstein → Eisenstein → ℂ := fun c u =>
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ t c)*
      MvPowerSeries.coeff (idealExponentOf u)
        (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
          metaplecticGaussIdealSeries r ℓ t)
  have hg := primary_cube_fiber_weighted_sum F (fun x => W (x/U)) hcut g
  change (∑ b ∈ primaryElementBall F, W (norm b/U)*
    ∑ n ∈ primaryCubeFiber F b, g (n 0) (n 1)) = _
  rw [hg]
  dsimp only [g]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcp,hcF⟩ := mem_primaryElementBall.mp hc
  have hcpos := norm_pos_of_ne_zero (primary_ne_zero hcp)
  have hcone := one_le_norm (primary_ne_zero hcp)
  have hX : 0 < U/norm c^3 := div_pos hU (pow_pos hcpos 3)
  have hXU : U/norm c^3 ≤ U := div_le_self hU.le (one_le_pow₀ hcone)
  have hXF : B*(U/norm c^3) ≤ F := (mul_le_mul_of_nonneg_left hXU hB).trans hBF
  rw [←metaplectic_completed_ideal_polynomial r ℓ W hX hXF hW t,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have he : norm (c^3*u)/U = norm u/(U/norm c^3) := by
    rw [norm_mul_eq,eisenstein_norm_pow]
    field_simp
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
