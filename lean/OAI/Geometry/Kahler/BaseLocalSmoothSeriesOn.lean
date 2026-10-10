import OAI.Geometry.Kahler.BasePotentialSmooth

namespace OAI

universe uKahler10148_1 uKahler10148_2 uKahler10162_1 uKahler10162_2 uKahler10184_1 uKahler10184_2

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma local_jet_series_derivative_on {E : Type uKahler10148_1} {F : Type uKahler10148_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {s : Set E} (hf : ∀ j y, y ∈ s → ContDiffAt ℝ ∞ (f j) y)
    (hs : IsOpen s) (hc : IsPreconnected s) {x : E} (hx : x ∈ s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    HasFDerivAt (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y)
      (∑' j, fderiv ℝ (iteratedFDeriv ℝ n (f j)) x) x := by
  apply hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hc
    (fun j y hy => ((hf j y hy).differentiableAt_iteratedFDeriv (by exact_mod_cast (ENat.natCast_lt_top n))).hasFDerivAt)
    (fun j y hy => ?_) hx
    (Summable.of_norm_bounded (hv n) (fun j => hb n j x hx)) hx
  simpa only [norm_fderiv_iteratedFDeriv] using hb (n+1) j y hy

lemma local_iteratedFDeriv_tsum_on {E : Type uKahler10162_1} {F : Type uKahler10162_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {s : Set E} (hf : ∀ j y, y ∈ s → ContDiffAt ℝ ∞ (f j) y)
    (hs : IsOpen s) (hc : IsPreconnected s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n (fun y => ∑' j, f j y))
      (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) s := by
  induction n with
  | zero =>
    intro x hx
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ n ih =>
    intro x hx
    have he : iteratedFDeriv ℝ n (fun y => ∑' j, f j y) =ᶠ[𝓝 x]
        (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hx) (fun y hy => ih hy)
    simp_rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    rw [he.fderiv_eq,(local_jet_series_derivative_on hf hs hc hx hv hb n).fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv.map_tsum

lemma local_contDiff_tsum_on {E : Type uKahler10184_1} {F : Type uKahler10184_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℕ → E → F} {s : Set E} (hf : ∀ j y, y ∈ s → ContDiffAt ℝ ∞ (f j) y)
    (hs : IsOpen s) (hc : IsPreconnected s)
    {v : ℕ → ℕ → ℝ} (hv : ∀ n, Summable (v n))
    (hb : ∀ n j y, y ∈ s → ‖iteratedFDeriv ℝ n (f j) y‖ ≤ v n j) :
    ContDiffOn ℝ ∞ (fun y => ∑' j, f j y) s := by
  apply contDiffOn_of_differentiableOn
  intro n hn x hx
  have he : iteratedFDerivWithin ℝ n (fun y => ∑' j, f j y) s =ᶠ[𝓝 x]
      (fun y => ∑' j, iteratedFDeriv ℝ n (f j) y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [iteratedFDerivWithin_of_isOpen n hs hy]
    exact local_iteratedFDeriv_tsum_on hf hs hc hv hb n hy
  exact ((local_jet_series_derivative_on hf hs hc hx hv hb n).differentiableAt.congr_of_eventuallyEq he).differentiableWithinAt

end PinchedHartogs.BaseConstruction

end

end OAI
