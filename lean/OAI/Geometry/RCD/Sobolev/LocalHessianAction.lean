import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # The local Hessian action and the exact two-center commutator identity

Gigli (2018), Theorem 3.3.8, equation (3.3.19), identifies the three-term
gradient formula with Hessian evaluation on gradient vector fields.
The cancellation below only uses the actual local Sobolev pairings.
-/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The three-term gradient formula for Hess f(grad v, grad u), when the
three local gradient pairings have Sobolev representatives. -/
def localHessianAction (f v u fv fu vu : SobolevSpace μ hQ) : X → ℝ :=
  fun x => (localGamma μ hQ v fu x + localGamma μ hQ u fv x -
    localGamma μ hQ f vu x) / 2

/-- The second derivatives of the coordinate function cancel exactly.
No differentiability of a pointwise metric is used. -/
theorem local_hessian_commutator {Ω : Set X} {f v u : SobolevSpace μ hQ}
    (Gfv : LocalHessianPairing μ hQ Ω f v)
    (Gvf : LocalHessianPairing μ hQ Ω v f)
    (Gfu : LocalHessianPairing μ hQ Ω f u)
    (Gvu : LocalHessianPairing μ hQ Ω v u) :
    (fun x => localGamma μ hQ v Gfu.mixed x - localGamma μ hQ f Gvu.mixed x) =ᵐ[μ.restrict Ω]
      fun x => localHessianAction μ hQ f v u Gfv.mixed Gfu.mixed Gvu.mixed x -
        localHessianAction μ hQ v f u Gvf.mixed Gvu.mixed Gfu.mixed x := by
  have heq : SobolevSpace.toLp μ hQ Gfv.mixed =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ hQ Gvf.mixed := by
    filter_upwards [Gfv.mixed_rep, Gvf.mixed_rep,
      ae_restrict_of_ae (localGamma_comm μ hQ f v)] with x hfv hvf hc
    exact hfv.trans (hc.trans hvf.symm)
  have hg := localGamma_pair_congr_ae μ hQ (f := u) (f' := u)
    (g := Gvf.mixed) (g' := Gfv.mixed) Filter.EventuallyEq.rfl heq
  filter_upwards [hg] with x hx
  dsimp only [localHessianAction]
  rw [hx]
  ring

end RegularPointCoordinates

end

end OAI
