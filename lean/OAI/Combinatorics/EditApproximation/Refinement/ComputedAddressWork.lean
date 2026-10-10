import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoAddressWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionWork
import OAI.Combinatorics.EditApproximation.Geometry.HeightPowerWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter



 theorem computedFamilyAddressWork_le (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyAddressWork source target N input ≤
      2 * (7 * intervalTreeDepth (integerParameters N).M source.length + 60) *
        (computedFamilyResult source target N input).requests :=
  rankedMemoAddressWork_le _ _ _ _ _ _
    (computedFamilyMemoCodeWithWork_cost source target N (inputHeight N ^ 2)) _ _

private theorem address_factor_bound (H J : ℕ) (hH : 100 ≤ H) (hJ : J ≤ H) :
    2 * (7 * J + 60) ≤ H ^ 2 := by nlinarith only [hH, hJ]

 theorem computedFamilyAddressWork_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      (computedFamilyAddressWork source target N input : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedFamilyResult_requests_near_linear (epsilon / 2) hh,
    fixed_height_power_subpolynomial 2 (epsilon / 2) hh,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)]
    with N hr hp hN hell
  intro source target hsize input
  have hdepth := computed_tree_depth_bound N source.length (by omega) (by omega) hell
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    nlinarith only [hdepth, hell]
  have hH : 100 ≤ inputHeight N := (by omega : 100 ≤ inputSmallLog N).trans
    (computed_smallLog_le_height N)
  have hfactor := address_factor_bound (inputHeight N) _ hH hJ
  have ha := computedFamilyAddressWork_le source target N input
  have haR : (computedFamilyAddressWork source target N input : ℝ) ≤
      (inputHeight N : ℝ) ^ 2 * (computedFamilyResult source target N input).requests := by
    exact_mod_cast ha.trans (Nat.mul_le_mul_right _ hfactor)
  calc
    _ ≤ (inputHeight N : ℝ) ^ 2 * (computedFamilyResult source target N input).requests := haR
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul hp (hr source target hsize input) (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
