import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.RadialCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RadialCoordinates
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open CoordinateGeometry

theorem metric_nonneg {B : MetricTensor E}
    (hp : ∀ v : E, v ≠ 0 → 0 < B v v) (v : E) : 0 ≤ B v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (hp v hv).le

theorem hasDerivAt_regularized_radius {B : MetricTensor E}
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, 0 ≤ B v v)
    {c : ℝ → E} {w : E} {t ε T : ℝ} (hε : 0 < ε) (hc : HasDerivAt c w t) :
    HasDerivAt (fun s => T * Real.sqrt (B (c s) (c s) + ε))
      (T * B (c t) w / Real.sqrt (B (c t) (c t) + ε)) t := by
  have hpos : 0 < B (c t) (c t) + ε := add_pos_of_nonneg_of_pos (hp _) hε
  have hd := (B.hasFDerivAt.comp_hasDerivAt t hc).clm_apply hc
  have hsqrt := ((hd.add_const ε).sqrt hpos.ne').const_mul T
  convert! hsqrt using 1
  simp only [Function.comp_apply, hs w (c t)]
  field_simp
  ring
end
end RadialCoordinates

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry RadialCoordinates
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

omit [FiniteDimensional ℝ E] in
 theorem base_mem (N : NormalFlow G S x₀) {x v : E} (hv : v ∈ (N.normalAt x).source) :
    x ∈ S := by
  have h0 := N.source_stays (x, v) hv 0 ⟨le_rfl, N.time_pos.le⟩
  have h := (N.ode _ h0).1
  simpa only [N.initial (x, v) h0] using h

omit [FiniteDimensional ℝ E] in
 theorem normalAt_mem (N : NormalFlow G S x₀) {x v : E}
    (hv : v ∈ (N.normalAt x).source) : N.normalAt x v ∈ S := by
  rw [normalAt_apply]
  exact (N.ode _ (N.source_stays (x, v) hv N.time ⟨N.time_pos.le, le_rfl⟩)).1

 theorem radial_derivative_bound (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x v : E} (hv : v ∈ (N.normalAt x).source) (w : E) {ε : ℝ} (hε : 0 < ε) :
    |N.time * G x v w / Real.sqrt (G x v v + ε)| ≤
      Real.sqrt (G (N.normalAt x v) (fderiv ℝ (N.normalAt x) v w)
        (fderiv ℝ (N.normalAt x) v w)) := by
  let D := fderiv ℝ (N.normalAt x) v
  let B := G (N.normalAt x v)
  have hB : ∀ u, 0 ≤ B u u := metric_nonneg (hpos _ (N.normalAt_mem hv))
  have hbase : 0 ≤ G x v v := metric_nonneg (hpos _ (N.base_mem hv)) v
  have hc := metric_cauchy_sq (hsym _ (N.normalAt_mem hv)) hB (D v) (D w)
  have hg := N.normalAt_gauss hS hG hsym hpos hv
  change (B (D v) (D w)) ^ 2 ≤ B (D v) (D v) * B (D w) (D w) at hc
  rw [show B (D v) (D w) = N.time ^ 2 * G x v w from hg w,
    show B (D v) (D v) = N.time ^ 2 * G x v v from hg v] at hc
  have hmain : N.time ^ 2 * (G x v w) ^ 2 ≤ G x v v * B (D w) (D w) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos N.time_pos)).mp
    convert! hc using 1 <;> ring
  have hsum : 0 < G x v v + ε := add_pos_of_nonneg_of_pos hbase hε
  apply Real.abs_le_sqrt
  rw [div_pow, Real.sq_sqrt hsum.le, mul_pow]
  apply (div_le_iff₀ hsum).mpr
  exact hmain.trans (by nlinarith only [hB (D w), hε])

theorem radial_along_curve (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} {c : ℝ → E} {c' : E} {t ε : ℝ} (hε : 0 < ε)
    (ht : c t ∈ (N.normalAt x).target) (hc : HasDerivAt c c' t) :
    ∃ d : ℝ,
      HasDerivAt (fun s => N.time * Real.sqrt
        (G x ((N.normalAt x).symm (c s)) ((N.normalAt x).symm (c s)) + ε)) d t ∧
      |d| ≤ Real.sqrt (G (c t) c' c') := by
  let e := N.normalAt x
  let v := e.symm (c t)
  have hv : v ∈ e.source := e.map_target ht
  have hdi := ((N.normalAt_inverse_smooth x _ ht).contDiffAt
    (e.open_target.mem_nhds ht)).differentiableAt (by simp)
  have hdv := hdi.hasFDerivAt.comp_hasDerivAt t hc
  let w := fderiv ℝ e.symm (c t) c'
  have hdv' : HasDerivAt (fun s => e.symm (c s)) w t := hdv
  have hdf := ((N.normalAt_smooth x _ hv).contDiffAt
    (e.open_source.mem_nhds hv)).differentiableAt (by simp)
  have hforward := hdf.hasFDerivAt.comp_hasDerivAt t hdv'
  have heq : (fun s => e (e.symm (c s))) =ᶠ[𝓝 t] c := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht)] with s hs
    exact e.right_inv hs
  have hD : fderiv ℝ e v w = c' :=
    (hforward.congr_of_eventuallyEq heq.symm).unique hc
  refine ⟨N.time * G x v w / Real.sqrt (G x v v + ε), ?_, ?_⟩
  · exact hasDerivAt_regularized_radius (hsym _ (N.base_mem hv))
      (metric_nonneg (hpos _ (N.base_mem hv))) hε hdv'
  · have hbound := N.radial_derivative_bound hS hG hsym hpos hv w hε
    change |N.time * G x v w / Real.sqrt (G x v v + ε)| ≤
      Real.sqrt (G (e v) (fderiv ℝ e v w) (fderiv ℝ e v w)) at hbound
    rw [hD, e.right_inv ht] at hbound
    exact hbound
end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
