import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeResolvent

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeResolvent_domain_error (r : ℝ) (hr : 0 < r) (a : hodgeEnergy A J α hs ht) :
    ‖hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a) -
      hodgeInclusion A J α hs ht a‖ ≤ r * ‖hodgeWeakDerivative A J α hs ht a‖ := by
  let i := hodgeInclusion A J α hs ht
  let D := hodgeWeakDerivative A J α hs ht
  let u := hodgeWeakSolution A J α hs ht r hr (i a)
  have he := hodgeWeakSolution_identity A J α hs ht r hr (i a) (u-a)
  have hi : hodgeResolvent A J α hs ht r (i a) = i u := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  change ⟪hodgeResolvent A J α hs ht r (i a),i (u-a)⟫ + r^2*⟪D u,D (u-a)⟫ = ⟪i a,i (u-a)⟫ at he
  rw [hi,map_sub,map_sub,inner_sub_right,inner_sub_right,inner_sub_right] at he
  have hn : ‖i u-i a‖^2 + r^2*‖D u‖^2 = r^2*⟪D u,D a⟫ := by
    rw [← real_inner_self_eq_norm_sq (i u-i a)]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq]
    rw [real_inner_comm (i a) (i u)] at he ⊢
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
    linarith
  have hc := mul_le_mul_of_nonneg_left (real_inner_le_norm (D u) (D a)) (sq_nonneg r)
  rw [hi]
  have hpos : 0 ≤ r * ‖D a‖ := mul_nonneg hr.le (norm_nonneg _)
  have hsquare := sq_nonneg (r*‖D u‖-r*‖D a‖)
  nlinarith [norm_nonneg (i u-i a)]

lemma hodgeResolvent_tendsto (f : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeResolvent A J α hs ht r f) (𝓝[>] 0) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := (hodgeInclusion_dense A J α hs ht).exists_dist_lt f (by positivity : 0 < ε/4)
  let D := hodgeWeakDerivative A J α hs ht a
  have hδ : 0 < ε/(2*(‖D‖+1)) := div_pos hε (by positivity)
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds hδ))] with r hr hsmall
  have hr' : 0 < r := hr
  have hsmallD : r * ‖D‖ < ε/2 := by
    have hb : r*(2*(‖D‖+1)) < ε := (lt_div_iff₀ (by positivity)).mp hsmall
    nlinarith [norm_nonneg D]
  rw [dist_eq_norm]
  have hx := hodgeResolvent_domain_error A J α hs ht r hr' a
  have hf := hodgeResolvent_norm_le A J α hs ht r (f-hodgeInclusion A J α hs ht a)
  rw [map_sub] at hf
  have htri := norm_add_le (hodgeResolvent A J α hs ht r f-
    hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a))
    (hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a)-hodgeInclusion A J α hs ht a)
  have htri2 := norm_add_le (hodgeResolvent A J α hs ht r f-hodgeInclusion A J α hs ht a)
    (hodgeInclusion A J α hs ht a-f)
  rw [sub_add_sub_cancel] at htri htri2
  rw [dist_eq_norm,norm_sub_rev] at ha
  have hn := norm_sub_rev (hodgeInclusion A J α hs ht a) f
  change r*‖hodgeWeakDerivative A J α hs ht a‖ < ε/2 at hsmallD
  linarith

lemma hodgeRegularization_error (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeRegularization A J α hs ht r f-f‖ ≤
      3*‖hodgeResolvent A J α hs ht r f-f‖ := by
  let R := hodgeResolvent A J α hs ht r
  have h1 : ‖R (R f)-R f‖ ≤ ‖R f-f‖ := by
    rw [← map_sub]; exact hodgeResolvent_norm_le A J α hs ht r _
  have h2 : ‖R (R (R f))-R (R f)‖ ≤ ‖R (R f)-R f‖ := by
    rw [← map_sub]; exact hodgeResolvent_norm_le A J α hs ht r _
  have ht1 := norm_add_le (R (R (R f))-R (R f)) (R (R f)-R f)
  have ht2 := norm_add_le (R (R (R f))-R f) (R f-f)
  rw [sub_add_sub_cancel] at ht1 ht2
  change ‖R (R (R f))-f‖ ≤ 3*‖R f-f‖
  linarith

lemma hodgeRegularization_tendsto (f : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeRegularization A J α hs ht r f) (𝓝[>] 0) (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (hodgeResolvent_tendsto A J α hs ht f).sub (tendsto_const_nhds (x := f))
  have hn := h.norm.const_mul 3
  simp only [sub_self,norm_zero,mul_zero] at hn
  exact squeeze_zero (fun r => norm_nonneg _)
    (fun r => hodgeRegularization_error A J α hs ht r f) hn
end TamingCompatibility.GeometricHilbert

end

end OAI
