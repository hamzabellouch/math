import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarIntervalStability
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! Uniform convergence of scalar Cauchy problems on a fixed interval follows
from uniform convergence of the coefficients and convergence of initial data. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralScalar_uniform_dependence
    (a b : ℝ) (V : ℕ → ℝ → ℂ) (W : ℝ → ℂ)
    (q : ℕ → ℝ → ℂ × ℂ) (p : ℝ → ℂ × ℂ)
    (hW : ContinuousOn W (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hpD : ∀ t ∈ Icc a b, HasDerivAt p (spectralScalarField (W t) (p t)) t)
    (hq : ∀ᶠ n in atTop, ContinuousOn (q n) (Icc a b) ∧
      ∀ t ∈ Icc a b, HasDerivAt (q n) (spectralScalarField (V n t) (q n t)) t)
    (hVW : TendstoUniformlyOn V W atTop (Icc a b))
    (hinit : Tendsto (fun n => q n a) atTop (𝓝 (p a))) :
    TendstoUniformlyOn q p atTop (Icc a b) := by
  obtain ⟨B₀,hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  obtain ⟨M₀,hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  let B := max B₀ 0 + 1
  let M := max M₀ 0
  let C := Real.exp ((1 + B) * (b - a))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hM : 0 ≤ M := le_max_right _ _
  have hC : 0 < C := Real.exp_pos _
  have hpb (t : ℝ) (ht : t ∈ Icc a b) : ‖p t‖ ≤ M :=
    (hM₀ t ht).trans (le_max_left _ _)
  have hinit' : Tendsto (fun n => ‖q n a - p a‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hinit.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => p a) atTop (𝓝 (p a)))).norm
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let delta := min 1 (eps / (4 * C * (M + 1)))
  have hd : 0 < delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hde : delta * (4 * C * (M + 1)) ≤ eps :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hi : 0 < eps / (2 * C) := by positivity
  filter_upwards [hq, (Metric.tendstoUniformlyOn_iff.mp hVW) delta hd,
    hinit'.eventually (gt_mem_nhds hi)] with n hqn hv hn t ht
  have hdiff (s : ℝ) (hs : s ∈ Icc a b) : ‖W s - V n s‖ ≤ delta := by
    simpa only [dist_eq_norm] using (hv s hs).le
  have hbound (s : ℝ) (hs : s ∈ Icc a b) : ‖V n s‖ ≤ B := by
    calc
      ‖V n s‖ ≤ ‖W s‖ + ‖W s - V n s‖ := norm_le_norm_add_norm_sub _ _
      _ ≤ max B₀ 0 + 1 := add_le_add ((hB₀ s hs).trans (le_max_left _ _))
        ((hdiff s hs).trans hd1)
      _ = B := rfl
  have hstab := spectralScalar_interval_stability a b B delta M hB hd.le hM
    (V n) W (q n) p hqn.1 hp hqn.2 hpD hbound hdiff hpb t ht
  have hden : 1 ≤ 1 + B := by linarith
  have hterm : delta * M / (1 + B) ≤ delta * (M + 1) := by
    calc
      delta * M / (1 + B) ≤ delta * M :=
        div_le_self (mul_nonneg hd.le hM) hden
      _ ≤ delta * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hd.le
  have hni : ‖q n a - p a‖ * (2 * C) < eps := (lt_div_iff₀ (by positivity)).mp hn
  have hsmall : (‖q n a - p a‖ + delta * M / (1 + B)) * C < eps := by
    have htC := mul_le_mul_of_nonneg_right hterm hC.le
    nlinarith
  rw [dist_eq_norm,norm_sub_rev]
  exact hstab.trans_lt hsmall

end DefocusingNLS

end OAI
