import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplier
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem commute_multiplier_of_represented
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun x => A x (ξ x))
    (g : Lp ℂ ∞ μ) : Commute T (multiplier g) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (multiplier g ξ), multiplier_coe g ξ,
    multiplier_coe g (T ξ), hT ξ] with x hTM hM hMT hTx
  change T (multiplier g ξ) x = multiplier g (T ξ) x
  rw [hTM, hM, hMT, hTx, map_smul]

theorem multiplier_star (g : Lp ℂ ∞ μ) :
    (multiplier (star g) : Lp E 2 μ →L[ℂ] Lp E 2 μ) =
      star (multiplier g : Lp E 2 μ →L[ℂ] Lp E 2 μ) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro ξ η
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_coe (star g) ξ, multiplier_coe g η,
    Lp.coeFn_star g] with x hx hy hg
  rw [hx, hy, hg]
  simp only [Pi.star_apply, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

theorem star_commutes_multiplier
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hT : ∀ g : Lp ℂ ∞ μ, Commute T (multiplier g))
    (g : Lp ℂ ∞ μ) : Commute (star T) (multiplier g) := by
  change star T * multiplier g = multiplier g * star T
  have h := congrArg star (hT (star g)).eq
  simpa only [star_mul, ← multiplier_star, star_star] using h.symm

end Invariant233.L2Multiplication

end

end OAI
