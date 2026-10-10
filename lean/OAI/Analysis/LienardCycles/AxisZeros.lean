import OAI.Analysis.LienardCycles.AxisFit

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
open PartialCalculus QuadraticCoordinates QuadraticFit RealAnalysis

def matchingDomain (a b : Fin 6 → ℝ) : Set ℝ := axisWidths a ∩ axisWidths b
noncomputable def matchingDelta (a b : Fin 6 → ℝ) (r : ℝ) : ℝ := axisM a r-axisM b r
lemma matchingDomain_open (a b : Fin 6 → ℝ) : IsOpen (matchingDomain a b) :=
  (axisWidths_open a).inter (axisWidths_open b)
lemma matchingDomain_ordConnected (a b : Fin 6 → ℝ) : OrdConnected (matchingDomain a b) :=
  (axisWidths_ordConnected a).inter (axisWidths_ordConnected b)
lemma matchingDelta_deriv (a b : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ matchingDomain a b) :
    HasDerivAt (matchingDelta a b) (axisV a r-axisV b r) r :=
  ((axisM_analytic a hr.1).differentiableAt (by simp)).hasDerivAt.sub
    ((axisM_analytic b hr.2).differentiableAt (by simp)).hasDerivAt
lemma axisV_conditional (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    axisV a r=conditionalV ((axisKappa a r,r),axisM a r) := by
  have hf := axisFit_spec a hr
  have hs := slope_eq (axisM_abs_lt a hr).1 (axisM_abs_lt a hr).2 hf.1
  dsimp only [conditionalV]
  rw [hs]
  exact hf.2.symm
lemma matchingDelta_crossing {a b : Fin 6 → ℝ} {r : ℝ} (hr : r ∈ matchingDomain a b)
    (hz : matchingDelta a b r=0) (hk : axisKappa b r<axisKappa a r) :
    0<axisV a r-axisV b r := by
  have hm : axisM a r=axisM b r := sub_eq_zero.mp hz
  rw [axisV_conditional a hr.1,axisV_conditional b hr.2,hm]
  exact sub_pos.mpr (conditionalV_strictMono (axisM_abs_lt b hr.2).1 (axisM_abs_lt b hr.2).2 hk)
lemma matchingDelta_zero_bound {a b : Fin 6 → ℝ}
    (hk : ∀ r ∈ matchingDomain a b, matchingDelta a b r=0 → axisKappa b r<axisKappa a r) :
    {r ∈ matchingDomain a b | matchingDelta a b r=0}.encard≤1 :=
  at_most_one_zero_of_deriv_pos (matchingDomain_ordConnected a b) (fun _ hr=>matchingDelta_deriv a b hr)
    (fun _ hr hz=>matchingDelta_crossing hr hz (hk _ hr hz))
lemma H_curvature_strictMono (d : ℝ) {r : ℝ} (hr : 0<r) : StrictMono (fun k=>H ((d,k),r)) := by
  apply strictMono_of_deriv_pos
  intro k
  rw [(Q_hasDerivAt hr).deriv]
  exact QuadraticVariation.Q_pos hr
lemma matchingDelta_kappa_of_lambda {a b : Fin 6 → ℝ} {r : ℝ} (hr : r ∈ matchingDomain a b)
    (hz : matchingDelta a b r=0) (hl : axisLambda a r<axisLambda b r) :
    axisKappa b r<axisKappa a r := by
  by_contra! hn
  have hp : 0<r := (axisM_abs_lt a hr.1).1
  have hmid := ((midpoint_strictMono (axisKappa a r) hp) hl).trans_le
    ((H_curvature_strictMono (axisLambda b r) hp).monotone hn)
  dsimp only at hmid
  rw [(axisFit_spec a hr.1).1,(axisFit_spec b hr.2).1] at hmid
  exact (ne_of_lt hmid) (sub_eq_zero.mp hz)
lemma matchingDelta_zero_bound_of_lambda {a b : Fin 6 → ℝ}
    (hl : ∀ r ∈ matchingDomain a b, axisLambda a r<axisLambda b r) :
    {r ∈ matchingDomain a b | matchingDelta a b r=0}.encard≤1 :=
  matchingDelta_zero_bound (fun r hr hz=>matchingDelta_kappa_of_lambda hr hz (hl r hr))
end QuinticLienard.AxisFlow

end OAI
