import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.RadialLength

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry RadialCoordinates
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

def coordinateLength (G : E → MetricTensor E) (c : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (G (c t) (deriv c t) (deriv c t)))

theorem regularized_radius_length (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} {c : ℝ → E} {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (hc : ContDiffOn ℝ 1 c (Icc a b))
    (hcN : ∀ t ∈ Icc a b, c t ∈ (N.normalAt x).target) :
    ‖N.time * Real.sqrt (G x ((N.normalAt x).symm (c b)) ((N.normalAt x).symm (c b)) + ε) -
      N.time * Real.sqrt (G x ((N.normalAt x).symm (c a)) ((N.normalAt x).symm (c a)) + ε)‖ₑ ≤
      coordinateLength G c a b := by
  let e := N.normalAt x
  let v : ℝ → E := fun t => e.symm (c t)
  let f : ℝ → ℝ := fun t => N.time * Real.sqrt (G x (v t) (v t) + ε)
  have hv : ContDiffOn ℝ 1 v (Icc a b) :=
    ((N.normalAt_inverse_smooth x).of_le (by simp)).comp hc hcN
  have hq : ContDiffOn ℝ 1 (fun t => G x (v t) (v t) + ε) (Icc a b) :=
    (((G x).contDiff.comp_contDiffOn hv).clm_apply hv).add contDiffOn_const
  have hqpos : ∀ t ∈ Icc a b, G x (v t) (v t) + ε ≠ 0 := by
    intro t ht
    have hn : 0 ≤ G x (v t) (v t) := metric_nonneg
      (hpos _ (N.base_mem (e.map_target (hcN t ht)))) _
    exact (add_pos_of_nonneg_of_pos hn hε).ne'
  have hf : ContDiffOn ℝ 1 f (Icc a b) := contDiffOn_const.mul (hq.sqrt hqpos)
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf hab).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hd := ((hc t ⟨ht.1.le, ht.2.le⟩).contDiffAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  obtain ⟨d, hdf, hbound⟩ := N.radial_along_curve hS hG hsym hpos hε
    (hcN t ⟨ht.1.le, ht.2.le⟩) hd.hasDerivAt
  have hdEq : deriv f t = d := hdf.deriv
  rw [hdEq, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal hbound

theorem radial_length (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} {c : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hc : ContDiffOn ℝ 1 c (Icc a b))
    (hcN : ∀ t ∈ Icc a b, c t ∈ (N.normalAt x).target) :
    ‖N.time * Real.sqrt (G x ((N.normalAt x).symm (c b)) ((N.normalAt x).symm (c b))) -
      N.time * Real.sqrt (G x ((N.normalAt x).symm (c a)) ((N.normalAt x).symm (c a)))‖ₑ ≤
      coordinateLength G c a b := by
  let v : ℝ → E := fun t => (N.normalAt x).symm (c t)
  let r : ℝ → ℝ≥0∞ := fun ε => ‖N.time * Real.sqrt (G x (v b) (v b) + ε) -
      N.time * Real.sqrt (G x (v a) (v a) + ε)‖ₑ
  have hr : Continuous r := by fun_prop
  have hlim : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 (r 0)) :=
    hr.continuousWithinAt.tendsto
  have hrle : r 0 ≤ coordinateLength G c a b := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact N.regularized_radius_length hS hG hsym hpos hab hε hc hcN
  simpa only [r, add_zero, v] using hrle

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
