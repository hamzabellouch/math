import OAI.Analysis.LienardCycles.AxisComparison

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open RealAnalysis ScaledProfile
lemma matchingDelta_zero_bound_of_third {a b : Fin 6 → ℝ}
    (ha : ∀ u,0<u → 0<third a u) (hb : ∀ u,0<u → third b u<0) :
    {r | IsIsolatedZeroOn (matchingDelta a b) (matchingDomain a b) r}.encard≤2 := by
  apply isolated_zero_count_linear (a:=secantA a b) (b:=secantB a b)
    (q:=fun r=>axisKappa a r-axisKappa b r) (matchingDomain_ordConnected a b)
    (fun _ hl _ hr _=>secantA_continuousOn hl hr)
  · intro r hr
    change HasDerivAt (matchingDelta a b) (secantA a b r*(axisM a r-axisM b r)+secantB a b r*(axisKappa a r-axisKappa b r)) r
    rw [←secant_identity hr]
    exact matchingDelta_deriv a b hr
  · exact fun _ hr=>secantB_pos hr
  · intro r hr s hs hrs
    exact sub_le_sub (axisKappa_monotone ha hr.1 hs.1 hrs)
      (axisKappa_antitone hb hr.2 hs.2 hrs)
end QuinticLienard.AxisFlow

end OAI
