import OAI.Analysis.CircleDomains.Selection.AnnularRadii
import OAI.Analysis.CircleDomains.Topology.DisjointCutoffAverages

namespace OAI

/-! Smooth planar cutoffs with arbitrarily small Dirichlet energy,
constructed by averaging disjoint concentric transition annuli. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def annularAverage (R : ℝ) (N : ℕ) : ℂ → ℝ :=
    cutoffAverage (fun i => dilatedCutoff unitAnnularCutoff (annularRadius R i)) N

 theorem annularAverage_smooth (R : ℝ) (N : ℕ) : ContDiff ℝ ∞ (annularAverage R N) :=
  cutoffAverage_smooth _ (fun _ => dilatedCutoff_smooth unitAnnularCutoff.contDiff _) N

 theorem annularAverage_compact {R : ℝ} (hR : 0 < R) (N : ℕ) :
    HasCompactSupport (annularAverage R N) :=
  cutoffAverage_compact _ (fun i => dilatedCutoff_compact unitAnnularCutoff.hasCompactSupport
    (annularRadius_pos hR i).ne') N

 theorem annularAverage_mem_unit (R : ℝ) {N : ℕ} (hN : 0 < N) (z : ℂ) :
    annularAverage R N z ∈ Icc (0 : ℝ) 1 :=
  cutoffAverage_mem_unit _ (fun _ _ => ⟨unitAnnularCutoff.nonneg, unitAnnularCutoff.le_one⟩) hN z

 theorem annularAverage_one {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : ‖z‖ ≤ annularRadius R N) : annularAverage R N z = 1 := by
  apply cutoffAverage_one _ hN
  intro i hi
  exact dilated_unitCutoff_one (annularRadius_pos hR i)
    (hz.trans (annularRadius_antitone hR.le (Finset.mem_range.mp hi).le))

 theorem annularAverage_tsupport {R : ℝ} (hR : 0 < R) (N : ℕ) :
    tsupport (annularAverage R N) ⊆ ball (0 : ℂ) R := by
  have hsub : support (annularAverage R N) ⊆ closedBall (0 : ℂ) (R/2) := by
    intro z hz
    by_contra hzout
    apply hz
    change (N : ℝ)⁻¹ * (∑ i ∈ Finset.range N, dilatedCutoff unitAnnularCutoff (annularRadius R i) z) = 0
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    by_contra hne
    have hzin := dilated_unitCutoff_support (annularRadius_pos hR i) hne
    have hb := annularRadius_antitone hR.le (Nat.zero_le i)
    have hzero : annularRadius R 0 = R/4 := by simp [annularRadius]
    rw [hzero] at hb
    apply hzout
    rw [mem_closedBall, dist_zero_right]
    have hzlt : ‖z‖ < 2*annularRadius R i := by simpa only [mem_ball, dist_zero_right] using hzin
    linarith
  have hcl : tsupport (annularAverage R N) ⊆ closedBall (0 : ℂ) (R/2) :=
    closure_minimal hsub isClosed_closedBall
  intro z hz
  have hh := hcl hz
  rw [mem_closedBall, dist_zero_right] at hh
  rw [mem_ball, dist_zero_right]
  linarith

 theorem annularAverage_energy {R : ℝ} (hR : 0 < R) {N : ℕ} (hN : 0 < N) :
    (∫ z, ‖fderiv ℝ (annularAverage R N) z‖^2) =
      (N : ℝ)⁻¹ * ∫ z, ‖fderiv ℝ (unitAnnularCutoff : ℂ → ℝ) z‖^2 := by
  apply cutoffAverage_energy _
    (fun _ => dilatedCutoff_smooth unitAnnularCutoff.contDiff _)
    (fun i => dilatedCutoff_compact unitAnnularCutoff.hasCompactSupport (annularRadius_pos hR i).ne')
    (annular_cutoff_derivatives_disjoint hR)
    (fun i => dilatedCutoff_energy
      ((unitAnnularCutoff.contDiff : ContDiff ℝ ∞ (unitAnnularCutoff : ℂ → ℝ)).differentiable (by simp))
      (annularRadius_pos hR i)) hN

 theorem exists_small_energy_cutoff_zero {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ball 0 R ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), f z = 1) ∧ (∫ z, ‖fderiv ℝ f z‖^2) < ε := by
  let C := ∫ z, ‖fderiv ℝ (unitAnnularCutoff : ℂ → ℝ) z‖^2
  have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
  obtain ⟨N, henergy, hN⟩ := ((ht.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop 0)).exists
  refine ⟨annularAverage R N, annularAverage_smooth R N, annularAverage_compact hR N,
    annularAverage_tsupport hR N, annularAverage_mem_unit R hN, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds (0 : ℂ) (annularRadius_pos hR N)] with z hz
    exact annularAverage_one hR hN (by simpa only [mem_ball, dist_zero_right] using (Metric.mem_ball.mp hz).le)
  · rw [annularAverage_energy hR hN]
    exact henergy

end CircleDomainRigidity

end

end OAI
