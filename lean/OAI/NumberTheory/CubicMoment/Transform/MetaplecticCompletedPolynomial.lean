import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletionCoefficient
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCubeFiberSum
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedBox

namespace OAI

/-! Exact identification of the completed ideal polynomial with the
original completed Gauss sum at every real height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_primal_weight_factor (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) (X t : ℝ) (c u : Eisenstein) :
    W (norm (c^3*u)/X)*(metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
      mellinPhase t (norm (metaplecticCubeProduct (c,u)))) =
        metaplecticPrimalCoefficient r ℓ W X (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  by_cases hcr : IsCoprime c r
  · simp only [metaplecticPrimalCoefficient,hcr,ite_true,mul_one,
      metaplecticCubeProduct]
    rw [show c^3*u = u*c^3 by ring]
    ring
  · simp [metaplecticPrimalCoefficient,hcr]

lemma metaplectic_completed_ideal_fibers
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X F t : ℝ) :
    (∑ b ∈ primaryElementBall F, W (norm b/X)*
      MvPowerSeries.coeff (idealExponentOf b)
        (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
          metaplecticGaussIdealSeries r ℓ t)) =
    ∑ b ∈ primaryElementBall F, W (norm b/X)*
      ∑ n ∈ primaryCubeFiber F b,
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (n 0,n 1)*
          mellinPhase t (norm (metaplecticCubeProduct (n 0,n 1))) := by
  apply Finset.sum_congr rfl
  intro b hb
  have hcoef := metaplectic_completed_primary_coefficient r ℓ t (b := b)
    (mem_primaryElementBall.mp hb).1 (F := F) (mem_primaryElementBall.mp hb).2
  exact congrArg (fun z : ℂ => W (norm b/X)*z) hcoef

lemma metaplectic_primal_weighted_fibers
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {X B F : ℝ}
    (hX : 0 < X) (hBF : B*X ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    (∑ b ∈ primaryElementBall F, W (norm b/X)*
      ∑ n ∈ primaryCubeFiber F b,
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (n 0,n 1)*
          mellinPhase t (norm (metaplecticCubeProduct (n 0,n 1)))) =
      metaplecticHeightCompleted r ℓ W X t := by
  have hcut : ∀ x : ℝ, F < x → W (x/X) = 0 := by
    intro x hx
    exact hW _ ((lt_div_iff₀ hX).mpr (hBF.trans_lt hx))
  let g : Eisenstein → Eisenstein → ℂ := fun c u =>
    metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
      mellinPhase t (norm (metaplecticCubeProduct (c,u)))
  have he := primary_cube_fiber_weighted_sum F (fun x => W (x/X)) hcut g
  change (∑ b ∈ primaryElementBall F, W (norm b/X)*
    ∑ n ∈ primaryCubeFiber F b, g (n 0) (n 1)) = _
  rw [he,metaplecticHeightCompleted_box r ℓ W hX hBF hW t]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro u _
  exact metaplectic_primal_weight_factor r ℓ W X t c u

theorem metaplectic_completed_ideal_polynomial
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) {X B F : ℝ}
    (hX : 0 < X) (hBF : B*X ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    (∑ b ∈ primaryElementBall F, W (norm b/X)*
      MvPowerSeries.coeff (idealExponentOf b)
        (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
          metaplecticGaussIdealSeries r ℓ t)) =
      metaplecticHeightCompleted r ℓ W X t :=
  (metaplectic_completed_ideal_fibers r ℓ W X F t).trans
    (metaplectic_primal_weighted_fibers r ℓ W hX hBF hW t)

end CubicFirstMoment

end

end OAI
