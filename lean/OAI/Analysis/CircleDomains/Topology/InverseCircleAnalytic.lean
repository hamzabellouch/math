import OAI.Analysis.CircleDomains.Topology.PrincipalCircleRemainder
import OAI.Analysis.CircleDomains.Rigidity.PrincipalCircleFluxLimit

namespace OAI

/-! The analytic germ supplies one common large-circle range for
smoothness and bounds of both the remainder and its derivative. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem analyticAt_on_inverse_circles {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0) :
    ∀ᶠ R : ℝ in atTop, 1 ≤ R ∧ ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹ := by
  obtain ⟨r, hr, hball⟩ := hT.exists_ball_analyticOnNhd
  filter_upwards [eventually_gt_atTop (max 1 r⁻¹)] with R hR
  have hRp : 0 < R := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hR)
  refine ⟨((le_max_left _ _).trans hR.le), ?_⟩
  intro t
  apply hball
  change dist (unitCircleParam 0 R t)⁻¹ 0 < r
  rw [dist_zero_right, norm_inv]
  simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hRp]
  exact (inv_lt_comm₀ hRp hr).mpr ((le_max_right _ _).trans_lt hR)

 theorem analytic_inverse_circle_bounds {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ᶠ R : ℝ in atTop,
      1 ≤ R ∧ ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹ ∧
        ‖T (unitCircleParam 0 R t)⁻¹‖ ≤ B ∧
        ‖deriv T (unitCircleParam 0 R t)⁻¹‖ ≤ C := by
  obtain ⟨B, RB, hB, hb⟩ := inverse_circle_remainder_bound hT.continuousAt
  obtain ⟨C, RC, hC, hc⟩ := inverse_circle_remainder_bound hT.deriv.continuousAt
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [analyticAt_on_inverse_circles hT, eventually_ge_atTop RB,
    eventually_ge_atTop RC] with R hA hRB hRC
  refine ⟨hA.1, ?_⟩
  intro t
  exact ⟨hA.2 t, (hb R hRB).2 t, (hc R hRC).2 t⟩

 theorem principalCircleRemainder_smooth {R : ℝ} (hR : 0 < R) {T : ℂ → ℂ}
    (hT : ∀ t : ℝ, AnalyticAt ℂ T (unitCircleParam 0 R t)⁻¹) :
    ContDiff ℝ (⊤ : ℕ∞) (principalCircleRemainder R T) := by
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (unitCircleParam 0 R) :=
    (contDiff_circleMap 0 R).comp (contDiff_const.mul contDiff_id)
  have hn (t : ℝ) : unitCircleParam 0 R t ≠ 0 := by
    have hh : ‖unitCircleParam 0 R t‖ = R := by
      simp only [unitCircleParam, norm_circleMap_zero, abs_of_pos hR]
    intro he
    rw [he, norm_zero] at hh
    linarith
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun t => (unitCircleParam 0 R t)⁻¹) := hγ.inv hn
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (hi.contDiffAt.pow 2).mul
    (((hT t).contDiffAt.restrict_scalars ℝ).comp t hi.contDiffAt)

end CircleDomainRigidity

end

end OAI
