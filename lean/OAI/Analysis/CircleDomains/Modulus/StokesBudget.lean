import OAI.Analysis.CircleDomains.Selection.AssignedStokes
import OAI.Analysis.CircleDomains.Modulus.FiniteBandNorm
import Mathlib.Topology.Order.LiminfLimsup

namespace OAI

/-! The finite Stokes estimate with distinct terminal labels and the actual
positive-excess budget. The second theorem performs the diagonal limit; its
hypotheses are the numerical estimates proved by finite transfer and Stokes. -/

open Set Function Filter
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity

 theorem circle_stokes_bound_of_excess
    {I S : Type*} [Fintype I] (label : I → S) (hinj : Injective label)
    (band : S → ℝ) (hband : Summable (fun s => band s ^ 2))
    (r A : I → ℝ) (hA : ∀ i, 0 ≤ A i) (hb : ∀ i, 0 ≤ band (label i))
    {L e η outer : ℝ} (hL : 0 ≤ L)
    (hr : ∑ i, r i ^ 2 ≤ L ^ 2)
    (hexcess : Real.sqrt (∑ i, max (A i - band (label i)) 0 ^ 2) ≤ η)
    (hstokes : |outer| ≤ Real.sqrt Real.pi * L * e +
      ∑ i, 2 * Real.pi * r i * A i) :
    |outer| ≤ Real.sqrt Real.pi * L * e +
      2 * Real.pi * L * (Real.sqrt (∑' s, band s ^ 2) + η) := by
  classical
  have hnorm := sqrt_sum_sq_le_of_excess_budget A (band ∘ label) hA hb
    (finite_label_band_norm_le label hinj band hband) hexcess
  have hcost := circle_costs_le_square_norm Finset.univ r A hL hr
  exact hstokes.trans (add_le_add le_rfl (hcost.trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))))

 theorem stokes_limsup_of_vanishing_errors
    (outer εE εA : ℕ → ℝ) {L E B : ℝ}
    (hεE : Tendsto εE atTop (𝓝 0)) (hεA : Tendsto εA atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, |outer n| ≤
      Real.sqrt Real.pi * L * (E + εE n) + 2 * Real.pi * L * (B + εA n)) :
    limsup (fun n => |outer n|) atTop ≤ Real.sqrt Real.pi * L * E + 2 * Real.pi * L * B := by
  have ht : Tendsto (fun n => Real.sqrt Real.pi * L * (E + εE n) +
      2 * Real.pi * L * (B + εA n)) atTop
      (𝓝 (Real.sqrt Real.pi * L * E + 2 * Real.pi * L * B)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.add hεE)).add
        (tendsto_const_nhds.mul (tendsto_const_nhds.add hεA))
  exact (limsup_le_limsup hbound
    (isCoboundedUnder_le_of_le atTop (fun n => abs_nonneg (outer n)))
    ht.isBoundedUnder_le).trans_eq ht.limsup_eq

end CircleDomainRigidity

end

end OAI
