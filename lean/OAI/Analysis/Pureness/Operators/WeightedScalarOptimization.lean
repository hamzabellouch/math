import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Set
open scoped Topology

theorem weighted_scalar_sqrt_bound (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ r : ℝ, r ≠ 0 → t ≤ (1+r*r)*a+(1+r⁻¹*r⁻¹)*b) :
    t ≤ (Real.sqrt a+Real.sqrt b)^2 := by
  have hδ (δ : ℝ) (hδ : 0 < δ) :
      t ≤ (Real.sqrt (a+δ)+Real.sqrt (b+δ))^2 := by
    let p := Real.sqrt (a+δ)
    let q := Real.sqrt (b+δ)
    have hp : 0 < p := Real.sqrt_pos.mpr (by linarith)
    have hq : 0 < q := Real.sqrt_pos.mpr (by linarith)
    have hp2 : p^2 = a+δ := Real.sq_sqrt (by linarith)
    have hq2 : q^2 = b+δ := Real.sq_sqrt (by linarith)
    let r := Real.sqrt (q/p)
    have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hq hp)
    have hrs : r*r = q/p := by simpa only [sq] using Real.sq_sqrt (div_pos hq hp).le
    have hri : r⁻¹*r⁻¹ = p/q := by rw [← mul_inv,hrs,inv_div]
    have ht := h r hr.ne'
    rw [hrs,hri] at ht
    calc
      t ≤ (1+q/p)*a+(1+p/q)*b := ht
      _ ≤ (1+q/p)*(a+δ)+(1+p/q)*(b+δ) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ = (p+q)^2 := by rw [← hp2,← hq2]; field_simp; ring
  have hc : Continuous (fun δ : ℝ => (Real.sqrt (a+δ)+Real.sqrt (b+δ))^2) := by fun_prop
  have ht := ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_iff.mpr (show {δ | t ≤ (Real.sqrt (a+δ)+Real.sqrt (b+δ))^2} ∈
      nhdsWithin (0 : ℝ) (Ioi 0) from
      Filter.mem_of_superset self_mem_nhdsWithin (fun δ hmem => hδ δ hmem)))
  simpa only [add_zero] using ht
end CuntzPureness

end

end OAI
