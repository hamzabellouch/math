import OAI.Geometry.RCD.Sobolev.LocalHessianAction

namespace OAI

/-! # The L2 commutator error from the actual Hessian actions -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The shifted Hessian of f and the ordinary Hessian of v control the
commutator error. The coordinate Hessian cancels in the exact identity. -/
theorem local_hessian_commutator_energy {Ω : Set X} {f v u : SobolevSpace μ hQ}
    (Gfv : LocalHessianPairing μ hQ Ω f v)
    (Gvf : LocalHessianPairing μ hQ Ω v f)
    (Gfu : LocalHessianPairing μ hQ Ω f u)
    (Gvu : LocalHessianPairing μ hQ Ω v u)
    (hF : MemLp (fun x => localHessianAction μ hQ f v u Gfv.mixed Gfu.mixed Gvu.mixed x -
      localGamma μ hQ v u x) 2 (μ.restrict Ω))
    (hV : MemLp (localHessianAction μ hQ v f u Gvf.mixed Gvu.mixed Gfu.mixed) 2 (μ.restrict Ω))
    {D E : ℝ}
    (hDF : (∫ x in Ω, (localHessianAction μ hQ f v u Gfv.mixed Gfu.mixed Gvu.mixed x -
      localGamma μ hQ v u x) ^ 2 ∂μ) ≤ D)
    (hDV : (∫ x in Ω, (localHessianAction μ hQ v f u Gvf.mixed Gvu.mixed Gfu.mixed x) ^ 2 ∂μ) ≤ E) :
    (∫ x in Ω, (localGamma μ hQ v Gfu.mixed x - localGamma μ hQ f Gvu.mixed x -
      localGamma μ hQ v u x) ^ 2 ∂μ) ≤ 2 * D + 2 * E := by
  let F := fun x => localHessianAction μ hQ f v u Gfv.mixed Gfu.mixed Gvu.mixed x -
    localGamma μ hQ v u x
  let H := localHessianAction μ hQ v f u Gvf.mixed Gvu.mixed Gfu.mixed
  have heq : (fun x => (localGamma μ hQ v Gfu.mixed x - localGamma μ hQ f Gvu.mixed x -
      localGamma μ hQ v u x) ^ 2) =ᵐ[μ.restrict Ω] fun x => (F x - H x) ^ 2 := by
    filter_upwards [local_hessian_commutator μ hQ Gfv Gvf Gfu Gvu] with x hx
    rw [hx]
    dsimp only [F, H]
    ring
  rw [integral_congr_ae heq]
  calc
    _ ≤ ∫ x in Ω, 2 * (F x) ^ 2 + 2 * (H x) ^ 2 ∂μ := by
      apply integral_mono_ae (hF.sub hV).integrable_sq
        ((hF.integrable_sq.const_mul 2).add (hV.integrable_sq.const_mul 2))
      exact Filter.Eventually.of_forall fun x => by
        change (F x - H x) ^ 2 ≤ 2 * (F x) ^ 2 + 2 * (H x) ^ 2
        nlinarith only [sq_nonneg (F x + H x)]
    _ = 2 * (∫ x in Ω, (F x) ^ 2 ∂μ) + 2 * (∫ x in Ω, (H x) ^ 2 ∂μ) := by
      rw [integral_add (hF.integrable_sq.const_mul 2) (hV.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hDF (by norm_num))
      (mul_le_mul_of_nonneg_left hDV (by norm_num))

end RegularPointCoordinates

end

end OAI
