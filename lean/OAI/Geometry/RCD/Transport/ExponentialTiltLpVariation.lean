import OAI.Geometry.RCD.Transport.ExponentialTiltVariation

namespace OAI

/-! # Strong L² differentiation of bounded exponential perturbations -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

 def exponentialTiltLp (r : Lp ℝ 2 μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) : Lp ℝ 2 μ :=
  lpMultiplier μ (boundedMultiplier μ (fun x => Real.exp (t*g x))
    (Real.measurable_exp.comp (measurable_const.mul hg))
    ⟨Real.exp (|t| *M),(Real.exp_pos _).le⟩ (fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hgb x))) r

 theorem exponentialTiltLp_coe (r : Lp ℝ 2 μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    exponentialTiltLp μ r hg hgb t =ᵐ[μ] fun x => Real.exp (t*g x)*r x := by
  unfold exponentialTiltLp
  have he := boundedMultiplier_coe μ (fun x => Real.exp (t*g x))
    (Real.measurable_exp.comp (measurable_const.mul hg))
    ⟨Real.exp (|t| *M),(Real.exp_pos _).le⟩ (fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hgb x))
  filter_upwards [lpMultiplier_coe μ _ r,he] with x hx he
  rw [hx,he]

 theorem exponentialTiltLp_zero (r : Lp ℝ 2 μ) {g : X → ℝ} (hg : Measurable g)
    {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) : exponentialTiltLp μ r hg hgb 0=r := by
  apply Lp.ext
  simpa only [zero_mul,Real.exp_zero,one_mul] using exponentialTiltLp_coe μ r hg hgb 0

 theorem exponentialTiltLp_hasDerivAt_zero (r : Lp ℝ 2 μ) {g : X → ℝ}
    (hg : Measurable g) {M : ℝ≥0} (hgb : ∀ x, |g x| ≤ M) :
    HasDerivAt (exponentialTiltLp μ r hg hgb)
      (lpMultiplier μ (boundedMultiplier μ g hg M hgb) r) 0 := by
  let v := lpMultiplier μ (boundedMultiplier μ g hg M hgb) r
  have hv : v =ᵐ[μ] fun x => g x*r x := by
    filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ g hg M hgb) r,
      boundedMultiplier_coe μ g hg M hgb] with x hx hy
    exact hx.trans (by rw [hy])
  have hb (t : ℝ) (ht : |t| *M ≤ 1) :
      ‖exponentialTiltLp μ r hg hgb t-r-t • v‖ ≤ (t^2*(M:ℝ)^2)*‖r‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [exponentialTiltLp_coe μ r hg hgb t,hv,
      Lp.coeFn_sub (exponentialTiltLp μ r hg hgb t-r) (t • v),
      Lp.coeFn_sub (exponentialTiltLp μ r hg hgb t) r,Lp.coeFn_smul t v] with x he hx hs hs' hsm
    rw [hs,Pi.sub_apply,hs',Pi.sub_apply,hsm,Pi.smul_apply,he,hx]
    change ‖Real.exp (t*g x)*r x-r x-t*(g x*r x)‖ ≤ _
    rw [show Real.exp (t*g x)*r x-r x-t*(g x*r x)=
      (Real.exp (t*g x)-1-t*g x)*r x by ring,norm_mul]
    have htg : ‖t*g x‖ ≤ |t| *M := by
      rw [norm_mul,Real.norm_eq_abs t,Real.norm_eq_abs (g x)]
      exact mul_le_mul_of_nonneg_left (hgb x) (abs_nonneg t)
    have hsq : ‖t*g x‖^2 ≤ t^2*(M:ℝ)^2 := by
      calc
        _ ≤ (|t| *M)^2 := pow_le_pow_left₀ (norm_nonneg _) htg 2
        _ = _ := by rw [mul_pow,sq_abs]
    exact mul_le_mul_of_nonneg_right
      ((Real.norm_exp_sub_one_sub_id_le (htg.trans ht)).trans hsq) (norm_nonneg _)
  rw [hasDerivAt_iff_tendsto]
  have he : ∀ᶠ t : ℝ in 𝓝 0, |t| *M ≤ 1 := by
    have hc : Continuous (fun t : ℝ => |t| *(M:ℝ)) := continuous_abs.mul continuous_const
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds (by simp : (fun t : ℝ => |t| *(M:ℝ)) 0<1))] with t ht
    exact ht.le
  have hupper : ∀ᶠ t : ℝ in 𝓝 0,
      ‖t-0‖⁻¹*‖exponentialTiltLp μ r hg hgb t-exponentialTiltLp μ r hg hgb 0-(t-0) • v‖ ≤
        |t| *(M:ℝ)^2*‖r‖ := by
    filter_upwards [he] with t ht
    rw [sub_zero,exponentialTiltLp_zero]
    by_cases hz : t=0
    · simp only [hz,norm_zero,inv_zero,zero_mul,abs_zero]
      exact le_rfl
    · calc
        _ ≤ ‖t‖⁻¹*((t^2*(M:ℝ)^2)*‖r‖) :=
          mul_le_mul_of_nonneg_left (hb t ht) (inv_nonneg.mpr (norm_nonneg _))
        _ = _ := by
          rw [Real.norm_eq_abs,←sq_abs t]
          field_simp [abs_ne_zero.mpr hz]
  apply squeeze_zero' (.of_forall fun _ => mul_nonneg
    (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hupper
  simpa only [abs_zero,zero_mul] using
    ((continuous_abs.tendsto 0).mul_const ((M:ℝ)^2)).mul_const ‖r‖

end RegularPointCoordinates

end

end OAI
