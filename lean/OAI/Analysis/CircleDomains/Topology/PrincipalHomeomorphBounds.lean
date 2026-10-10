import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Quantitative bounds for a principally normalized plane homeomorphism.
A topological plane homeomorphism cannot maximize its image norm in the
interior of a disk. No holomorphic assumption inside the disk is used. -/
open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma homeomorph_disk_bound (F : ℂ ≃ₜ ℂ) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ z, ‖z‖ = r → ‖F z‖ ≤ M) :
    ∀ z, ‖z‖ ≤ r → ‖F z‖ ≤ M := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn
    (nonempty_closedBall.mpr hr.le) F.continuous.norm.continuousOn
  have hxn : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hxbound : ‖F x‖ ≤ M := by
    by_contra hn
    have hnorm : 0 < ‖F x‖ := lt_of_le_of_lt hM (lt_of_not_ge hn)
    have hxlt : ‖x‖ < r := lt_of_le_of_ne hxn (fun he => hn (hb x he))
    have hnhds : closedBall (0 : ℂ) r ∈ 𝓝 x :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds (by
        simpa only [mem_ball, dist_zero_right] using hxlt)) ball_subset_closedBall
    have hl : IsLocalMax (fun z => ‖F z‖) x := hmax.isLocalMax hnhds
    have hsq : IsLocalMax (fun z => ‖F z‖^2) x := by
      filter_upwards [hl] with z hz
      nlinarith [norm_nonneg (F z), norm_nonneg (F x)]
    have hsq' : IsLocalMax (fun z : ℂ => ‖z‖^2) (F x) := by
      have hsq'' : IsLocalMax (fun z => ‖F z‖^2) (F.symm (F x)) := by
        simpa only [F.symm_apply_apply] using hsq
      simpa only [Function.comp_def, F.apply_symm_apply] using
        hsq''.comp_continuous F.symm.continuous.continuousAt
    have he := hsq'.hasFDerivAt_eq_zero (hasStrictFDerivAt_norm_sq (F x)).hasFDerivAt
    have hz := congrArg (fun L : ℂ →L[ℝ] ℝ => L (F x)) he
    simp only [two_smul, add_apply, innerSL_apply_apply,
      zero_apply, real_inner_self_eq_norm_sq] at hz
    nlinarith
  intro z hz
  exact (hmax (by simpa only [mem_closedBall, dist_zero_right] using hz)).trans hxbound

lemma principal_homeomorph_pointwise_bounds (F : ℂ ≃ₜ ℂ) {R : ℝ} (hR : 0 < R)
    (hb : ∀ z, 2*R ≤ ‖z‖ → ‖F z-z‖ ≤ R) :
    (∀ z, ‖F z‖ ≤ max (3*R) (‖z‖+R)) ∧
      ∀ w, ‖F.symm w‖ ≤ max (2*R) (‖w‖+R) := by
  have hinner : ∀ z, ‖z‖ ≤ 2*R → ‖F z‖ ≤ 3*R := by
    apply homeomorph_disk_bound F (by positivity) (by positivity)
    intro z hz
    have := hb z hz.ge
    have := norm_le_norm_sub_add (F z) z
    linarith
  constructor
  · intro z
    by_cases hz : 2*R ≤ ‖z‖
    · apply le_trans _ (le_max_right _ _)
      linarith [norm_le_norm_sub_add (F z) z, hb z hz]
    · exact (hinner z (le_of_not_ge hz)).trans (le_max_left _ _)
  · intro w
    by_cases hw : 2*R ≤ ‖F.symm w‖
    · have hh := hb (F.symm w) hw
      rw [F.apply_symm_apply] at hh
      have hn := norm_le_norm_sub_add (F.symm w) w
      rw [norm_sub_rev] at hn
      apply le_trans _ (le_max_right _ _)
      linarith
    · exact (le_of_not_ge hw).trans (le_max_left _ _)

lemma principal_homeomorph_displacement_bound (F : ℂ ≃ₜ ℂ) {R : ℝ} (hR : 0 < R)
    (hb : ∀ z, 2*R ≤ ‖z‖ → ‖F z-z‖ ≤ R) :
    ∀ z, ‖F z-z‖ ≤ 5*R := by
  intro z
  by_cases hz : 2*R ≤ ‖z‖
  · exact (hb z hz).trans (by linarith)
  · have hzn : ‖z‖ < 2*R := lt_of_not_ge hz
    have hF := (principal_homeomorph_pointwise_bounds F hR hb).1 z
    have hm : max (3*R) (‖z‖+R) = 3*R := max_eq_left (by linarith)
    rw [hm] at hF
    exact (norm_sub_le (F z) z).trans (by linarith)

end CircleDomainRigidity

end

end OAI
