import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.Young
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff
import OAI.Geometry.WeakHessian.Sobolev.QuadraticCheegerEnergyComparable
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatEntropyHopf
import OAI.Geometry.WeakHessian.Sobolev.WeakGradientContactDistance
import OAI.Geometry.WeakHessian.Transport.RerouteFiniteSubplanShort
import OAI.Geometry.WeakHessian.Geodesics.Join
import OAI.Geometry.WeakHessian.Sobolev.AnySubgradient
import OAI.Geometry.WeakHessian.Calculus.CompactEVI
import OAI.Geometry.WeakHessian.LocalBounds.SharpPointwise
import OAI.Geometry.WeakHessian.HeatFlow.HeatCZero
import OAI.Geometry.WeakHessian.Sobolev.LaplacianChain
import OAI.Geometry.WeakHessian.LocalBounds.OriginalCoreProducer
import OAI.Geometry.WeakHessian.HeatFlow.GeneratorEnergyDifferentiation
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatSmoothing
import OAI.Geometry.WeakHessian.Transport.WeightedPlanHamiltonJacobi
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHopfHeatCommutation
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatTransportCoupling
import OAI.Geometry.WeakHessian.Entropy.IntervalEntropyDual
import OAI.Geometry.WeakHessian.Transport.TwoCouplingCost
import OAI.Geometry.WeakHessian.Calculus.LocalDistribution

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem every_geodesic [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (m : Measure X) (K N : ℝ) (hN : 1 < N)
    (hfull : FullSupport m) (hfinite : FiniteOnBoundedSets m) (hrcd : RCD m K N)
    (F G : X → ℝ) (hFbound : BoundedFunction F) (hFlip : GloballyLipschitz F)
    (hGbound : BoundedFunction G) (hGcont : Continuous G)
    (hHess : WeakHessianUpperBound m F G)
    (σ : Curve X) (hσ : IsGeodesic σ) : CurveSecondDerivativeBound F G σ := by
  let : ProperSpace X := properSpace_of_cd hN hrcd.1 hfull hfinite
  let : SigmaFinite m := sigmaFinite_of_finiteOnBoundedSets m hfinite (σ timeZero)
  obtain ⟨CF,hCF⟩ := hFbound
  obtain ⟨L,hL⟩ := hFlip
  obtain ⟨CG,hCG⟩ := hGbound
  apply local_midpoint_implies_curve_bound hL.continuous hGcont _ σ hσ
  intro γ hγ R c hR hshort hlocal
  exact hHess.rcd_local_midpoint hN hrcd hfull hfinite hL hCF hCG hGcont γ hγ hR hshort hlocal

end WeakHessian

end
end

end OAI
