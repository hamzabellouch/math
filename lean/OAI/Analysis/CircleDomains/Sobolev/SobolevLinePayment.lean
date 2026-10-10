import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneLinePayment
import OAI.Analysis.CircleDomains.Sobolev.PhysicalCoordinateLines
import OAI.Analysis.CircleDomains.Sobolev.MollificationEnergy
import OAI.Analysis.CircleDomains.Sobolev.UniformLocalMollification

namespace OAI

/-! Continuous compact Sobolev barriers pay for every transverse line
on which they attain one. Uniform mollification supplies the line FTC;
strong convergence of weak partials passes the energy bound to the limit. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_coordinate_line_payment
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    (W : DeGiorgi.MemW1pWitness 2 v univ)
    {L : ℝ} (hL : 0 < L) (hs : tsupport v ⊆ ball 0 L)
    (i : Fin 2) {J : Set ℝ} (hJ : MeasurableSet J) (hJL : J ⊆ Icc (-L) L)
    (hcross : ∀ y ∈ J, ∃ c ∈ Icc (-L) L, v (physicalCoordinateLine i y c) = 1) :
    (volume J).toReal/(8*L) ≤ ∫ x, ‖W.weakGrad x‖^2 := by
  have hcompact : HasCompactSupport v :=
    (isCompact_closedBall (0 : EuclideanPlane) L).of_isClosed_subset (isClosed_tsupport v)
      (hs.trans ball_subset_closedBall)
  have hvLp : MemLp v 2 volume := by simpa only [Measure.restrict_univ] using W.memLp
  have happrox := planarMollification_uniform_on_compact hvLp.aestronglyMeasurable
    (isCompact_closedBall (0 : EuclideanPlane) (2*L)) isOpen_univ (subset_univ _)
    hv.continuousOn (show (0 : ℝ) < 1/8 by norm_num)
  have hnorm (y x : ℝ) (hy : y ∈ Icc (-L) L) (hx : x ∈ Icc (-L) L) :
      physicalCoordinateLine i y x ∈ closedBall 0 (2*L) := by
    rw [mem_closedBall_zero_iff]
    exact (physicalCoordinateLine_norm_le i y x).trans (by
      have hx' : |x| ≤ L := abs_le.mpr hx
      have hy' : |y| ≤ L := abs_le.mpr hy
      linarith)
  have hzero (y : ℝ) : v (physicalCoordinateLine i y (-L)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hb := mem_ball_zero_iff.mp (hs hx)
    have ha := PiLp.norm_apply_le (physicalCoordinateLine i y (-L)) i
    rw [physicalCoordinateLine_coordinate,Real.norm_eq_abs,abs_neg,abs_of_pos hL] at ha
    exact (not_lt_of_ge ha) hb
  have hpay : ∀ᶠ n in atTop, (volume J).toReal/(8*L) ≤
      ∫ x, (fderiv ℝ (planarMollification v n) x (EuclideanSpace.single i 1))^2 := by
    filter_upwards [happrox] with n hn
    have hf := planarMollification_smooth (hvLp.locallyIntegrable (by norm_num)) n
    rw [← physicalCoordinateLine_energy_eq (hf.of_le (by simp)) i]
    apply smooth_plane_half_payment hL
      (fun y => (hf.comp (physicalCoordinateLine_contDiff i y)).of_le (by simp))
      (physicalCoordinateLine_energy_integrable (hf.of_le (by simp)) i
        (planarMollification_partial_memLp W hcompact n i).integrable_sq) hJ
      (ne_of_lt ((measure_mono hJL).trans_lt measure_Icc_lt_top))
    filter_upwards [ae_restrict_mem hJ] with y hy
    obtain ⟨c,hc,hvc⟩ := hcross y hy
    refine ⟨c,hc,?_⟩
    have hec := hn _ (hnorm y c (hJL hy) hc)
    have hea := hn _ (hnorm y (-L) (hJL hy) ⟨le_rfl,by linarith⟩)
    rw [hvc] at hec
    rw [hzero y] at hea
    change (1:ℝ)/2 ≤ planarMollification v n (physicalCoordinateLine i y c) -
      planarMollification v n (physicalCoordinateLine i y (-L))
    have hc' := (abs_lt.mp hec).1
    have ha' := (abs_lt.mp hea).2
    linarith
  have hgrad : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  have hlim := integral_sq_tendsto_of_L2
    (fun n => planarMollification_partial_memLp W hcompact n i) hgrad
    (planarMollification_tendsto_gradient_L2 W i)
  refine (ge_of_tendsto hlim hpay).trans ?_
  have hn : Integrable (fun x => ‖W.weakGrad x‖^2) volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_norm_memLp.integrable_sq
  apply integral_mono_ae hgrad.integrable_sq hn
  exact Eventually.of_forall fun x => by
    have hi := PiLp.norm_apply_le (W.weakGrad x) i
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hi 2

end CircleDomainRigidity

end

end OAI
