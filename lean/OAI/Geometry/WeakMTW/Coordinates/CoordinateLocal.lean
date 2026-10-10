import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateGeometry

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem geodesic_energy_on_connected {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U) {q : ℝ → E × E}
    (hq : ∀ t ∈ U, (q t).1 ∈ S ∧ HasDerivAt q (geodesicSpray G (q t)) t)
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) :
    G (q s).1 (q s).2 (q s).2 = G (q t).1 (q t).2 (q t).2 := by
  have hd : ∀ r ∈ U, HasDerivAt (fun z => G (q z).1 (q z).2 (q z).2) 0 r := by
    intro r hr
    exact geodesic_energy_hasDerivAt_zero hS hG hsym hpos
      (hq r hr).1 (hq r hr).2.fst (hq r hr).2.snd
  exact hU.is_const_of_deriv_eq_zero hUc
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

omit [FiniteDimensional ℝ E] in
theorem radial_scale_radius (B : MetricTensor E) (v : E) {T : ℝ} (hT : 0 < T) (a : ℝ) :
    T * Real.sqrt (B ((a / T) • v) ((a / T) • v)) = |a| * Real.sqrt (B v v) := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [show a / T * (a / T * B v v) = (a / T) ^ 2 * B v v by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, ← mul_assoc,
    abs_div, abs_of_pos hT]
  congr 1
  field_simp

end
end CoordinateGeometry

namespace NormalNeighborhood
open Set
 theorem affine_time_mem_convex {U : Set ℝ} (hU : Convex ℝ U)
    {s r T t : ℝ} (hs : s ∈ U) (hr : r ∈ U) (hT : 0 < T) (ht : t ∈ Icc (0 : ℝ) T) :
    s + (r - s) / T * t ∈ U := by
  have hθ : t / T ≤ 1 := (div_le_one hT).mpr ht.2
  have h := hU hs hr (sub_nonneg.mpr hθ) (div_nonneg ht.1 hT.le)
    (show (1 - t / T) + t / T = 1 by ring)
  convert! h using 1
  simp only [smul_eq_mul]
  ring
end NormalNeighborhood
end

end WeakMTWGlobalSupport

end OAI
