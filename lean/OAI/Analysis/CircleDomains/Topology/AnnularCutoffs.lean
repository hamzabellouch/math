import OAI.Analysis.CircleDomains.Sobolev.ScaledCutoffEnergy

namespace OAI

/-! Concentric smooth cutoffs whose transition annuli are disjoint.
Each dilation has the same Dirichlet energy in dimension two. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def unitAnnularCutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

 theorem dilated_unitCutoff_one {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    dilatedCutoff unitAnnularCutoff r z = 1 := by
  apply unitAnnularCutoff.one_of_mem_closedBall
  simp only [unitAnnularCutoff, mem_closedBall, dist_zero_right]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hz)

 theorem dilated_unitCutoff_support {r : ℝ} (hr : 0 < r) :
    support (dilatedCutoff unitAnnularCutoff r) ⊆ ball (0 : ℂ) (2*r) := by
  intro z hz
  have hh : r⁻¹ • z ∈ support (unitAnnularCutoff : ℂ → ℝ) := hz
  rw [unitAnnularCutoff.support_eq] at hh
  simp only [unitAnnularCutoff, mem_ball, dist_zero_right] at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hh
  have hn := (inv_mul_lt_iff₀ hr).mp hh
  simpa only [mem_ball, dist_zero_right, mul_comm] using hn

 theorem dilated_unitCutoff_derivative_annulus {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : fderiv ℝ (dilatedCutoff unitAnnularCutoff r) z ≠ 0) :
    r ≤ ‖z‖ ∧ ‖z‖ ≤ 2*r := by
  have hd : fderiv ℝ (unitAnnularCutoff : ℂ → ℝ) (r⁻¹ • z) ≠ 0 := by
    intro hh
    apply hz
    rw [dilatedCutoff_fderiv ((unitAnnularCutoff.contDiff : ContDiff ℝ ∞ (unitAnnularCutoff : ℂ → ℝ)).differentiable (by simp)), hh, smul_zero]
  constructor
  · by_contra hn
    have hsmall : r⁻¹ • z ∈ ball (0 : ℂ) unitAnnularCutoff.rIn := by
      simp only [unitAnnularCutoff, mem_ball, dist_zero_right]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_lt_iff₀ hr).mpr (by simpa using (lt_of_not_ge hn))
    have he := unitAnnularCutoff.eventuallyEq_one_of_mem_ball hsmall
    exact hd (by simpa using he.fderiv_eq)
  · have hm := support_fderiv_subset ℝ hd
    rw [unitAnnularCutoff.tsupport_eq] at hm
    simp only [unitAnnularCutoff, mem_closedBall, dist_zero_right] at hm
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hm
    simpa only [mul_comm] using (inv_mul_le_iff₀ hr).mp hm

 theorem separated_dilatedCutoff_derivatives
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : 2*r < s) (z : ℂ) :
    fderiv ℝ (dilatedCutoff unitAnnularCutoff r) z = 0 ∨
      fderiv ℝ (dilatedCutoff unitAnnularCutoff s) z = 0 := by
  by_cases hz : fderiv ℝ (dilatedCutoff unitAnnularCutoff r) z = 0
  · exact Or.inl hz
  · right
    by_contra hw
    have ha := dilated_unitCutoff_derivative_annulus hr hz
    have hb := dilated_unitCutoff_derivative_annulus hs hw
    linarith

end CircleDomainRigidity

end

end OAI
