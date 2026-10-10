import OAI.Geometry.SurfaceImmersion.Geometry.TransverseSupport
import OAI.Geometry.SurfaceImmersion.Atlas.FlatTransverseCutoff

namespace OAI

/-! The supported ruled correction tends to zero globally in C1. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem narrowedRuling_C1_bound {f : Base → ProjectionTarget 3} {η : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : Base,
      ‖narrowedRuling f η r x‖ ≤ D*r ∧ ‖fderiv ℝ (narrowedRuling f η r) x‖ ≤ D*r := by
  obtain ⟨ρ,hρ,hsupp⟩ := narrowedRuling_fixed_ball f hc
  let R := rulingRemainder f η
  have hR : ContDiff ℝ ∞ R := rulingRemainder_smooth hf hη
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Base) ρ).exists_bound_of_continuousOn
    ((hR.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).continuousOn
  have hbound : ∀ x ∈ closedBall (0 : Base) ρ, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ |C| :=
    fun x hx => (hC x hx).trans (le_abs_self C)
  obtain ⟨B,hB,hcut⟩ := flat_transverse_cutoff_bound
  let D := (B+1)*(|C|+1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hCD : |C| ≤ D := by dsimp [D]; nlinarith [abs_nonneg C]
  have hBCD : (B+1)*|C| ≤ D := by dsimp [D]; nlinarith
  refine ⟨D,hD,?_⟩
  intro r hr hr1 x
  by_cases hx : x ∈ closedBall (0 : Base) ρ
  · obtain ⟨hv,hd⟩ := hcut R hR (rulingRemainder_axis f η)
      (rulingRemainder_first_jet hf hη) ρ |C| (abs_nonneg C) hbound r hr x hx
    constructor
    · exact hv.trans (by nlinarith [mul_nonneg (abs_nonneg C) hr.le])
    · exact hd.trans (mul_le_mul_of_nonneg_right hBCD hr.le)
  · have hn : x ∉ tsupport (narrowedRuling f η r) := fun ht => hx (hsupp r hr hr1 ht)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    rw [he.self_of_nhds,he.fderiv_eq]
    simp only [Pi.zero_apply,norm_zero,fderiv_zero]
    exact ⟨mul_nonneg hD.le hr.le,mul_nonneg hD.le hr.le⟩

theorem narrowedRuling_small {f : Base → ProjectionTarget 3} {η : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ r ≤ 1 ∧
      ∀ x : Base, ‖narrowedRuling f η r x‖ < ε ∧
        ‖fderiv ℝ (narrowedRuling f η r) x‖ < ε := by
  obtain ⟨D,hD,hbound⟩ := narrowedRuling_C1_bound hf hη hc
  let r := min (min ρ 1) (ε/(2*D))
  have hr : 0 < r := lt_min (lt_min hρ zero_lt_one) (div_pos hε (by positivity))
  have hrρ : r ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hDr : D*r < ε := by
    have he := (mul_le_mul_of_nonneg_left (min_le_right (min ρ 1) (ε/(2*D))) hD.le)
    have hid : D*(ε/(2*D)) = ε/2 := by field_simp
    rw [hid] at he
    linarith
  exact ⟨r,hr,hrρ,hr1,fun x => ⟨((hbound r hr hr1 x).1).trans_lt hDr,
    ((hbound r hr hr1 x).2).trans_lt hDr⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
