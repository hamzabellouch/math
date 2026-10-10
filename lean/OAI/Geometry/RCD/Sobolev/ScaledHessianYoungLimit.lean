import OAI.Geometry.RCD.Harmonic.WeightedDirectionalVanishing

namespace OAI

/-! # The canonical Young estimate at a shrinking physical scale -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem scaled_hessian_young_limit {Y : Type*}
    (r m S : ℕ → ℝ) (A : ℕ → Y → ℝ) {C : ℝ}
    (hr : ∀ k, 0 < r k) (hm : ∀ k, 0 < m k) (hC : 0 ≤ C)
    (hA : ∀ k y, 0 ≤ A k y)
    (hS : Tendsto (fun k => (r k)^2*S k/m k) atTop (𝓝 0))
    (hb : ∀ k y a, 0 < a →
      4*a*A k y ≤ 4*a^2*m k+C*(r k)^4*S k) :
    TendstoUniformly (fun k y => A k y/(r k*m k)) (fun _ => 0) atTop := by
  apply tendstoUniformly_of_directional_bound (C := 1) (M := C) zero_le_one hC
    (fun k y => div_nonneg (hA k y) (mul_nonneg (hr k).le (hm k).le))
    (E := fun k (_ : Y) => (r k)^2*S k/m k)
  · apply Metric.tendstoUniformly_iff.mpr
    intro e he
    filter_upwards [Metric.tendsto_nhds.mp hS e he] with k hk y
    simpa only [dist_comm] using hk
  · intro k y a ha
    apply (mul_le_mul_iff_right₀ (mul_pos (sq_pos_of_pos (hr k)) (hm k))).mp
    have hh := hb k y (r k*a) (mul_pos (hr k) ha)
    convert hh using 1 <;> field_simp [(hr k).ne',(hm k).ne']

end RegularPointCoordinates

end

end OAI
