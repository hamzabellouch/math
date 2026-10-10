import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTerminalUniqueness
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! Stable backward propagation of spectral columns across a fixed annulus. -/

open Set Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectral_backward_difference_bound (L R K ε : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (f g f' g' : ℝ → E₄) (hf : ContinuousOn f (Icc L R)) (hg : ContinuousOn g (Icc L R))
    (hfd : ∀ t ∈ Icc L R, HasDerivAt f (f' t) t)
    (hgd : ∀ t ∈ Icc L R, HasDerivAt g (g' t) t)
    (hb : ∀ t ∈ Icc L R, ‖f' t-g' t‖ ≤ K*‖f t-g t‖+ε)
    (r : ℝ) (hr : r ∈ Icc L R) :
    ‖f r-g r‖ ≤ (‖f R-g R‖+ε/K)*Real.exp (K*(R-L)) := by
  let V := fun t => f (R-t)-g (R-t)
  let D := fun t => -(f' (R-t)-g' (R-t))
  have hm (t : ℝ) (ht : t ∈ Icc 0 (R-L)) : R-t ∈ Icc L R := by
    constructor <;> linarith [ht.1,ht.2]
  have hV : ContinuousOn V (Icc 0 (R-L)) := (hf.sub hg).comp
    (continuous_const.sub continuous_id).continuousOn hm
  have hd : ∀ t ∈ Ico 0 (R-L), HasDerivWithinAt V (D t) (Ici t) t := by
    intro t ht
    have h := ((hfd (R-t) (hm t ⟨ht.1,ht.2.le⟩)).sub
      (hgd (R-t) (hm t ⟨ht.1,ht.2.le⟩))).scomp t ((hasDerivAt_id t).const_sub R)
    simpa only [V,D,Function.comp_def,neg_one_smul] using! h.hasDerivWithinAt
  have hbound : ∀ t ∈ Ico 0 (R-L), ‖D t‖ ≤ K*‖V t‖+ε := by
    intro t ht
    simpa only [D,V,norm_neg] using hb (R-t) (hm t ⟨ht.1,ht.2.le⟩)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hV hd
    (le_refl ‖V 0‖) hbound (R-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩
  simp only [V,sub_zero,sub_sub_cancel,gronwallBound_of_K_ne_0 hK.ne'] at h
  calc
    ‖f r-g r‖ ≤ ‖f R-g R‖*Real.exp (K*(R-r)) +
        ε/K*(Real.exp (K*(R-r))-1) := h
    _ ≤ (‖f R-g R‖+ε/K)*Real.exp (K*(R-r)) := by
      have := div_nonneg hε hK.le
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hr.1]) hK.le))
      (add_nonneg (norm_nonneg _) (div_nonneg hε hK.le))

theorem spectral_backward_uniform_limit (L R K : ℝ) (hK : 0 < K)
    (f f' : ℕ → ℝ → E₄) (g g' : ℝ → E₄) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hend : Tendsto (fun n => f n R) atTop (𝓝 (g R)))
    (hc : ∀ᶠ n in atTop, ContinuousOn (f n) (Icc L R)) (hgc : ContinuousOn g (Icc L R))
    (hfd : ∀ᶠ n in atTop, ∀ t ∈ Icc L R, HasDerivAt (f n) (f' n t) t)
    (hgd : ∀ t, t ∈ Icc L R → HasDerivAt g (g' t) t)
    (hb : ∀ᶠ n in atTop, 0 ≤ ε n ∧
      ∀ t ∈ Icc L R, ‖f' n t-g' t‖ ≤ K*‖f n t-g t‖+ε n) :
    TendstoUniformlyOn f g atTop (Icc L R) := by
  have he : Tendsto (fun n => ‖f n R-g R‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hend
  have hrate : Tendsto (fun n => (‖f n R-g R‖+ε n/K)*Real.exp (K*(R-L)))
      atTop (𝓝 0) := by
    simpa only [zero_div,add_zero,zero_mul] using
      (he.add (hε.div_const K)).mul_const (Real.exp (K*(R-L)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hb,hrate.eventually (gt_mem_nhds hδ),hc,hfd] with n hn hr hcn hdn t ht
  rw [dist_comm,dist_eq_norm]
  exact (spectral_backward_difference_bound L R K (ε n) hK hn.1 (f n) g (f' n) g'
    hcn hgc hdn hgd hn.2 t ht).trans_lt hr

end DefocusingNLS

end OAI
