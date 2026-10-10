import OAI.NumberTheory.CubicMoment.Transform.MetaplecticActualInverse
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! A literal point-count bound for the original smooth angular Gauss
sum, valid also below the first nonzero norm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem metaplecticAngularSmoothSum_trivial {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) {V B M : ℝ} (hV : 0 < V) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hcut : ∀ x : ℝ, B < x → W x = 0) (hW : ∀ x, ‖W x‖ ≤ M) :
    ‖metaplecticAngularSmoothSum r ℓ W V 0‖ ≤ 18*B*M*V := by
  rw [metaplecticAngularSmoothSum_finite r ℓ W hV (le_refl (B*V)) hcut 0]
  have hb (u : Eisenstein) (hu : u ∈ primaryElementBall (B*V)) :
      ‖W (norm u/V)*(gauss (r*u)*theta ℓ (r*u)*mellinPhase 0 (norm u))‖ ≤ M := by
    have hp := primary_mul hr (mem_primaryElementBall.mp hu).1
    simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one,
      norm_mul,norm_theta (primary_ne_zero hp),mul_one]
    exact (mul_le_mul_of_nonneg_left (norm_gauss_le_one hp) (_root_.norm_nonneg _)).trans
      (by simpa only [mul_one] using hW (norm u/V))
  calc
    _ ≤ ∑ u ∈ primaryElementBall (B*V), M :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hb)
    _ = ((primaryElementBall (B*V)).card:ℝ)*M := by simp
    _ ≤ (18*(B*V))*M := mul_le_mul_of_nonneg_right
      (primaryElementBall_card_le (mul_nonneg hB hV.le)) hM
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
