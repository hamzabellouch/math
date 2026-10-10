import OAI.Analysis.Pureness.Operators.WeightedScalarOptimization
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Set
open scoped Topology

theorem weighted_scalar_cube_bound (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ r : ℝ, r ≠ 0 → t ≤
      (Real.sqrt ((1+r*r)*a)+Real.sqrt ((1+r⁻¹*r⁻¹)*b))^2) :
    t ≤ (a^((3:ℝ)⁻¹)+b^((3:ℝ)⁻¹))^3 := by
  have hδ (δ : ℝ) (hδ : 0 < δ) :
      t ≤ ((a+δ)^((3:ℝ)⁻¹)+(b+δ)^((3:ℝ)⁻¹))^3 := by
    let p := (a+δ)^((3:ℝ)⁻¹)
    let q := (b+δ)^((3:ℝ)⁻¹)
    have hp : 0 < p := Real.rpow_pos_of_pos (by linarith) _
    have hq : 0 < q := Real.rpow_pos_of_pos (by linarith) _
    have hp3 : p^3 = a+δ := Real.rpow_inv_natCast_pow (by linarith) (by norm_num)
    have hq3 : q^3 = b+δ := Real.rpow_inv_natCast_pow (by linarith) (by norm_num)
    let r := Real.sqrt (q/p)
    have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hq hp)
    have hrs : r*r = q/p := by simpa only [sq] using Real.sq_sqrt (div_pos hq hp).le
    have hri : r⁻¹*r⁻¹ = p/q := by rw [← mul_inv,hrs,inv_div]
    have he1 : (1+q/p)*(a+δ) = (p*Real.sqrt (p+q))^2 := by
      rw [← hp3,mul_pow,Real.sq_sqrt (by positivity)]
      field_simp
    have he2 : (1+p/q)*(b+δ) = (q*Real.sqrt (p+q))^2 := by
      rw [← hq3,mul_pow,Real.sq_sqrt (by positivity)]
      field_simp
      ring
    have ht := h r hr.ne'
    rw [hrs,hri] at ht
    calc
      t ≤ (Real.sqrt ((1+q/p)*a)+Real.sqrt ((1+p/q)*b))^2 := ht
      _ ≤ (Real.sqrt ((1+q/p)*(a+δ))+Real.sqrt ((1+p/q)*(b+δ)))^2 := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
        exact add_le_add
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
          (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
      _ = (p+q)^3 := by
        rw [he1,he2,Real.sqrt_sq (by positivity),Real.sqrt_sq (by positivity),
          ← add_mul,mul_pow,Real.sq_sqrt (by positivity)]
        ring
  have hc : Continuous (fun δ : ℝ => ((a+δ)^((3:ℝ)⁻¹)+(b+δ)^((3:ℝ)⁻¹))^3) := by
    fun_prop (disch := positivity)
  have ht := ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_iff.mpr (show {δ | t ≤ ((a+δ)^((3:ℝ)⁻¹)+(b+δ)^((3:ℝ)⁻¹))^3} ∈
      nhdsWithin (0 : ℝ) (Ioi 0) from
      Filter.mem_of_superset self_mem_nhdsWithin (fun δ hmem => hδ δ hmem)))
  simpa only [add_zero] using ht
end CuntzPureness

end

end OAI
