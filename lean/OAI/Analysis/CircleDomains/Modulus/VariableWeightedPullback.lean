import OAI.Analysis.CircleDomains.Sobolev.SmoothWeightedL2Pullback

namespace OAI

/-! Uniform distortion suffices for strong L2 convergence under a varying
sequence of smooth weighted pullbacks. This applies to the actual inverse
principal approximants in the reflection-conjugacy calculation. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma exists_strong_variable_weighted_pullback (P : ℕ → ℂ ≃ₜ ℂ)
    (hP : ∀n,ContDiff ℝ ∞ (P n : ℂ → ℂ))
    (hPi : ∀n,ContDiff ℝ ∞ ((P n).symm : ℂ → ℂ))
    {K : ℝ} (hK : 0≤K)
    (hD : ∀n z,‖fderiv ℝ (P n : ℂ → ℂ) z‖^2≤K*|(fderiv ℝ (P n : ℂ → ℂ) z).det|)
    (e : ℕ → PlaneL2) (he : Tendsto e atTop (𝓝 0)) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧
      ∀n,∀ᵐz ∂volume,q n z=e n (P n z)*star (partialZ (P n) z) := by
  let f (n : ℕ) (z : ℂ) := e n (P n z)*star (partialZ (P n) z)
  have hh (n : ℕ) := smooth_weighted_L2_pullback (P n) (hP n) (hPi n) hK (hD n) (Lp.memLp (e n)) MeasurableSet.univ
  have hf (n : ℕ) : MemLp (f n) 2 volume := by simpa only [Measure.restrict_univ] using (hh n).1
  let q (n : ℕ) := (hf n).toLp (f n)
  have hb (n : ℕ) : ‖q n‖≤(K+1)*‖e n‖ := by
    have hi := (hh n).2
    have hq : (∫z,‖f n z‖^2)=‖q n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hf n).coeFn_toLp] with z hz
      rw [hz,real_inner_self_eq_norm_sq]
    have heq : (∫z,‖e n z‖^2)=‖e n‖^2 := by
      rw [←real_inner_self_eq_norm_sq,L2.inner_def]
      exact integral_congr_ae (.of_forall fun z => (real_inner_self_eq_norm_sq (e n z)).symm)
    have his : ‖q n‖^2≤K*‖e n‖^2 := by
      change (∫z in Set.univ,‖f n z‖^2)≤K*(∫z in P n '' Set.univ,‖e n z‖^2) at hi
      simpa only [image_univ,(P n).surjective.range_eq,Measure.restrict_univ,hq,heq] using hi
    have hk : K≤(K+1)^2 := by nlinarith [sq_nonneg K]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
    rw [mul_pow]
    exact his.trans (mul_le_mul_of_nonneg_right hk (sq_nonneg _))
  refine ⟨q,?_,fun n => (hf n).coeFn_toLp⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [norm_zero,mul_zero] using (he.norm.const_mul (K+1))

end CircleDomainRigidity

end

end OAI
