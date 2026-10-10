import OAI.Analysis.LienardCycles.CoefficientCases

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
open ScaledProfile RealAnalysis
lemma matching_isolated_case2 {a : Fin 6 → ℝ} (h1 : 0≤a 1) (h3 : a 3<0) (h5 : 0≤a 5) :
    {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}.encard≤2 := by
  apply matchingDelta_zero_bound_of_third (fun _ hh=>third_pos_case2 h1 h3 h5 hh)
  intro h hh
  rw [reflectX_third a hh]
  exact neg_neg_of_pos (third_pos_case2 h1 h3 h5 hh)
lemma matching_case3_gap {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : 0≤a 3) (h5 : 0≤a 5)
    {r : ℝ} (hr : r ∈ matchingDomain a (reflectX a)) : axisKappa (reflectX a) r<axisKappa a r := by
  let T := max (axisPeak a r) (axisPeak (reflectX a) r)+1
  have hTa : axisPeak a r<T := by dsimp [T]; linarith [le_max_left (axisPeak a r) (axisPeak (reflectX a) r)]
  have hTb : axisPeak (reflectX a) r<T := by dsimp [T]; linarith [le_max_right (axisPeak a r) (axisPeak (reflectX a) r)]
  have hT : 0<T := (axisPeak_spec a hr.1).1.1.trans hTa
  let δ := (-a 1)/(root T)^3
  have hδ : 0<δ := div_pos (neg_pos.mpr h1) (pow_pos (root_pos hT) _)
  have ha : 8*a 4+δ≤axisKappa a r := axisKappa_lower hr.1 hTa (fun _ hu=>curvature_lower_case3 h1 h3 h5 hu.1 hu.2)
  have hb : axisKappa (reflectX a) r≤8*a 4-δ := axisKappa_upper hr.2 hTb (fun h hu=>by
    rw [reflectX_curvature a hu.1]
    linarith [curvature_lower_case3 h1 h3 h5 hu.1 hu.2])
  linarith
lemma matching_zeros_case3 {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : 0≤a 3) (h5 : 0≤a 5) :
    {r ∈ matchingDomain a (reflectX a) | matchingDelta a (reflectX a) r=0}.encard≤1 :=
  matchingDelta_zero_bound (fun _ hr _=>matching_case3_gap h1 h3 h5 hr)
lemma matching_zeros_case4 {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : a 3<0) (h5 : 0≤a 5) :
    {r ∈ matchingDomain a (reflectX a) | matchingDelta a (reflectX a) r=0}.encard≤1 := by
  apply matchingDelta_zero_bound_of_lambda
  intro r hr
  have ha := axisLambda_lt hr.1 (fun _ hh=>intercept_pos_case4 h1 h3 h5 hh) (slope_atBot h1)
  have hb := axisLambda_gt (d:=2*a 2) hr.2 (fun h hh=>by
    rw [reflectX_intercept a hh]
    exact neg_neg_of_pos (intercept_pos_case4 h1 h3 h5 hh))
    (slope_atTop (a:=reflectX a) (by simpa using neg_pos.mpr h1))
  exact ha.trans hb
lemma matching_isolated_case3 {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : 0≤a 3) (h5 : 0≤a 5) :
    {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}.encard≤2 := by
  have hs : {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r} ⊆
      {r ∈ matchingDomain a (reflectX a) | matchingDelta a (reflectX a) r=0} := fun _ hr=>⟨hr.1,hr.2.1⟩
  exact (encard_mono hs).trans ((matching_zeros_case3 h1 h3 h5).trans (by norm_num))
lemma matching_isolated_case4 {a : Fin 6 → ℝ} (h1 : a 1<0) (h3 : a 3<0) (h5 : 0≤a 5) :
    {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}.encard≤2 := by
  have hs : {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r} ⊆
      {r ∈ matchingDomain a (reflectX a) | matchingDelta a (reflectX a) r=0} := fun _ hr=>⟨hr.1,hr.2.1⟩
  exact (encard_mono hs).trans ((matching_zeros_case4 h1 h3 h5).trans (by norm_num))
end QuinticLienard.AxisFlow

end OAI
