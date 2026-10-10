import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTerminalUniqueness
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! Finite-interval stability for the exterior ODE continuation. -/

open Set Filter
namespace DefocusingNLS

theorem radial_finite_difference_bound (T K ε : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (f g f' g' : ℝ → ℂ × ℂ) (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hfd : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hgd : ∀ t ∈ Icc 0 T, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Icc 0 T, ‖f' t-g' t‖ ≤ K*‖f t-g t‖+ε)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖f t-g t‖ ≤ (‖f 0-g 0‖+ε/K)*Real.exp (K*T) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (hf.sub hg)
    (fun s hs => ((hfd s ⟨hs.1,hs.2.le⟩).sub (hgd s ⟨hs.1,hs.2.le⟩)).hasDerivWithinAt)
    (le_refl ‖f 0-g 0‖) (fun s hs => hbound s ⟨hs.1,hs.2.le⟩) t ht
  simp only [sub_zero,gronwallBound_of_K_ne_0 hK.ne'] at h
  calc
    _ ≤ ‖f 0-g 0‖*Real.exp (K*t)+ε/K*(Real.exp (K*t)-1) := h
    _ ≤ (‖f 0-g 0‖+ε/K)*Real.exp (K*t) := by
      have := div_nonneg hε hK.le
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK.le))
      (add_nonneg (norm_nonneg _) (div_nonneg hε hK.le))

theorem radial_finite_uniform_limit (T K : ℝ) (hK : 0 < K)
    (f f' : ℕ → ℝ → ℂ × ℂ) (g g' : ℝ → ℂ × ℂ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hinit : Tendsto (fun n => f n 0) atTop (nhds (g 0)))
    (hc : ∀ n, ContinuousOn (f n) (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hfd : ∀ n t, t ∈ Icc 0 T → HasDerivAt (f n) (f' n t) t)
    (hgd : ∀ t, t ∈ Icc 0 T → HasDerivAt g (g' t) t)
    (hb : ∀ᶠ n in atTop, 0 ≤ ε n ∧
      ∀ t ∈ Icc 0 T, ‖f' n t-g' t‖ ≤ K*‖f n t-g t‖+ε n) :
    TendstoUniformlyOn f g atTop (Icc 0 T) := by
  have hi : Tendsto (fun n => ‖f n 0-g 0‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hinit
  have hrate : Tendsto (fun n => (‖f n 0-g 0‖+ε n/K)*Real.exp (K*T)) atTop (nhds 0) := by
    convert (hi.add (hε.div_const K)).mul_const (Real.exp (K*T)) using 1
    simp
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hb,hrate.eventually (gt_mem_nhds hδ)] with n hn hr t ht
  rw [dist_comm,dist_eq_norm]
  exact (radial_finite_difference_bound T K (ε n) hK hn.1 (f n) g (f' n) g'
    (hc n) hgc (hfd n) hgd hn.2 t ht).trans_lt hr

end DefocusingNLS

end OAI
