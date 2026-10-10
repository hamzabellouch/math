import OAI.Analysis.CircleDomains.Topology.PlanarMaximalInput

namespace OAI

/-! A maximal-function majorant pays the mass on a balloon by its mass
on any measurable subset occupying a fixed fraction of the balloon. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem ball_subset_double_ball {c x : ℂ} {d : ℝ} (hx : x ∈ ball c d) :
    ball c d ⊆ ball x (2*d) := by
  intro y hy
  rw [mem_ball] at hx hy ⊢
  calc
    dist y x ≤ dist y c+dist c x := dist_triangle _ _ _
    _ < d+d := add_lt_add hy (by simpa only [dist_comm] using hx)
    _ = 2*d := by ring

 theorem maximal_ball_payment {g m : ℂ → ℝ}
    (hg : MemLp g 2 volume) (hm : MemLp m 2 volume) (_hm0 : ∀ z, 0 ≤ m z)
    (hmax : ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume,
      (∫ y in ball x r, ‖g y‖) ≤ volume.real (ball x r)*m x)
    {c : ℂ} {d k : ℝ} (hd : 0 < d) (_hk : 0 < k) {E : Set ℂ}
    (hE : MeasurableSet E) (hEB : E ⊆ ball c d)
    (hsize : k*d^2 ≤ volume.real E) :
    k*(∫ y in ball c d, ‖g y‖) ≤ 4*Real.pi*(∫ x in E, m x) := by
  have hEf : volume E ≠ ∞ := measure_ne_top_of_subset hEB measure_ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hEf
  have hmE : IntegrableOn m E := (hm.restrict E).integrable (by norm_num)
  have hpoint : ∀ᵐ x ∂volume.restrict E,
      (∫ y in ball c d, ‖g y‖) ≤ (4*Real.pi*d^2)*m x := by
    filter_upwards [ae_restrict_mem hE,ae_restrict_of_ae (hmax (2*d) (by positivity))] with x hx hxmax
    have hbig : IntegrableOn (fun y => ‖g y‖) (ball x (2*d)) :=
      ((hg.norm.locallyIntegrable (by norm_num)).integrableOn_isCompact
        (isCompact_closedBall x (2*d))).mono_set ball_subset_closedBall
    calc
      _ ≤ ∫ y in ball x (2*d), ‖g y‖ :=
        setIntegral_mono_set hbig (Eventually.of_forall (fun _ => norm_nonneg _))
          (Filter.Eventually.of_forall (ball_subset_double_ball (hEB hx)))
      _ ≤ volume.real (ball x (2*d))*m x := hxmax
      _ = _ := by rw [show volume.real (ball x (2*d)) = Real.pi*(2*d)^2 from
          real_volume_ball x (by positivity)]; ring
  have hi := integral_mono_ae (integrable_const (∫ y in ball c d, ‖g y‖))
    (hmE.const_mul (4*Real.pi*d^2)) hpoint
  rw [integral_const,integral_const_mul,smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hi
  have hI : 0 ≤ ∫ y in ball c d, ‖g y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hl := (mul_le_mul_of_nonneg_right hsize hI).trans hi
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hd)).mp
  nlinarith only [hl]

end CircleDomainRigidity

end

end OAI
