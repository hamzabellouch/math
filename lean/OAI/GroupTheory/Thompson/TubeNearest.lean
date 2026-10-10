import OAI.GroupTheory.Thompson.TubeRegularCurve
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Global nearest points obtained by compact parameter minimization

No properness of the ambient inner-product space is required. Separation of
the curve confines minimization to a compact interval in its real parameter.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic.RegularCurveData

open Set Filter
open scoped InnerProductSpace Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (C : RegularCurveData E)

/-- The predicate of being a global nearest parameter for the actual curve. -/
def IsNearest (x : E) (s : ℝ) : Prop :=
  ∀ t : ℝ, ‖x - C.curve s‖ ≤ ‖x - C.curve t‖

/-- The separation estimate makes the residual strictly larger away from a
compact interval around any initial tube witness. -/
theorem residual_gt_of_far {x : E} {s t : ℝ}
    (hs : ‖x - C.curve s‖ < C.rho) (hst : (1 / 32 : ℝ) ≤ |t - s|) :
    3 * C.rho < ‖x - C.curve t‖ := by
  have hsep := C.separated s t hst
  have htri : ‖C.curve t - C.curve s‖ ≤
      ‖x - C.curve t‖ + ‖x - C.curve s‖ := by
    calc
      ‖C.curve t - C.curve s‖ ≤
          ‖C.curve t - x‖ + ‖x - C.curve s‖ := by
        simpa only [dist_eq_norm] using dist_triangle (C.curve t) x (C.curve s)
      _ = ‖x - C.curve t‖ + ‖x - C.curve s‖ := by
        rw [norm_sub_rev (C.curve t) x]
  have := C.four_rho_lt_separation
  linarith

/-- A tube point has a global nearest parameter, attained by minimizing on a
compact interval of real parameters. -/
theorem nearest_exists (x : E) (hx : x ∈ C.tube) :
    ∃ s : ℝ, C.IsNearest x s ∧ ‖x - C.curve s‖ < C.rho := by
  obtain ⟨z, ⟨t₀, rfl⟩, ht₀⟩ :=
    (Metric.infDist_lt_iff C.range_nonempty).mp hx
  have ht₀' : ‖x - C.curve t₀‖ < C.rho := by
    simpa only [dist_eq_norm] using ht₀
  have ht₀mem : t₀ ∈ Icc (t₀ - 1 / 32) (t₀ + 1 / 32) := by
    constructor <;> linarith
  have hcont : Continuous (fun t : ℝ => ‖x - C.curve t‖) :=
    (continuous_const.sub C.continuous_curve).norm
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨t₀, ht₀mem⟩
    hcont.continuousOn
  have hsclose : ‖x - C.curve s‖ < C.rho :=
    lt_of_le_of_lt (hmin ht₀mem) ht₀'
  refine ⟨s, ?_, hsclose⟩
  intro t
  by_cases ht : t ∈ Icc (t₀ - 1 / 32) (t₀ + 1 / 32)
  · exact hmin ht
  · have hfar : (1 / 32 : ℝ) ≤ |t - t₀| := by
      by_contra h
      have hnear := abs_lt.mp (lt_of_not_ge h)
      exact ht ⟨by linarith [hnear.1], by linarith [hnear.2]⟩
    have hlarge := C.residual_gt_of_far ht₀' hfar
    have := C.rho_pos
    linarith

/-- Every global minimizer has exactly the distance-to-range residual. -/
theorem nearest_norm_eq_infDist {x : E} {s : ℝ} (hs : C.IsNearest x s) :
    ‖x - C.curve s‖ = Metric.infDist x (range C.curve) := by
  apply le_antisymm
  · apply (Metric.le_infDist C.range_nonempty).mpr
    rintro y ⟨t, rfl⟩
    simpa only [dist_eq_norm] using hs t
  · simpa only [dist_eq_norm] using
      Metric.infDist_le_dist_of_mem (x := x) (mem_range_self s)

/-- Differentiating the squared residual at its global minimum proves
orthogonality to the tangent. -/
theorem nearest_perp_tangent {x : E} {s : ℝ} (hs : C.IsNearest x s) :
    ⟪x - C.curve s, C.tangent s⟫_ℝ = 0 := by
  have hsquare : IsMinOn (fun t : ℝ => ‖x - C.curve t‖ ^ 2) univ s := by
    apply isMinOn_univ_iff.mpr
    intro t
    exact pow_le_pow_left₀ (norm_nonneg _) (hs t) 2
  have hlocal : IsLocalMin (fun t : ℝ => ‖x - C.curve t‖ ^ 2) s :=
    hsquare.isLocalMin (by simp)
  have hderiv : HasDerivAt (fun t : ℝ => ‖x - C.curve t‖ ^ 2)
      (2 * ⟪x - C.curve s, -C.velocity s⟫_ℝ) s :=
    ((C.hasDerivAt s).const_sub x).norm_sq
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  have hspeed : ‖C.velocity s‖ ≠ 0 := by
    have := C.speed_lower s
    linarith
  rw [inner_neg_right, C.velocity_eq s, real_inner_smul_right] at hzero
  have hproduct : ‖C.velocity s‖ * ⟪x - C.curve s, C.tangent s⟫_ℝ = 0 := by
    linarith
  exact (mul_eq_zero.mp hproduct).resolve_left hspeed

end ThompsonNonamenability.Analytic.RegularCurveData

end

end OAI
