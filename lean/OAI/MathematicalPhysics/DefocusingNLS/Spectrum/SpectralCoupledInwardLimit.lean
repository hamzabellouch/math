import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledInwardDecay
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! Uniformly bounded scaled data give a vanishing inward channel across
a shell of positive width as the spectral scale escapes. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralComplex_coupled_inward_limit (a mu eps : ℕ → ℝ) (B gap M : ℝ)
    (hgap : 0 < gap) (hM : 0 ≤ M) (hmu : Tendsto mu atTop atTop)
    (heps : Tendsto eps atTop (𝓝 0))
    (q dq w alpha : ℕ → ℝ → ℂ)
    (hdata : ∀ᶠ n in atTop, gap ≤ B-a n ∧ 0 ≤ eps n ∧
      ContinuousOn (q n) (Icc (a n) B) ∧ ‖q n (a n)‖ ≤ M ∧
      (∀ r ∈ Ioo (a n) B, HasDerivAt (q n) (dq n r) r) ∧
      (∀ r ∈ Ioo (a n) B, (alpha n r).re ≤ -mu n) ∧
      (∀ r ∈ Ioo (a n) B,
        ‖dq n r-alpha n r*q n r‖ ≤ eps n*mu n*(‖q n r‖+‖w n r‖)) ∧
      ∀ r ∈ Ioo (a n) B, ‖w n r‖ ≤ M) :
    Tendsto (fun n => q n B) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n => Real.exp (-(mu n*gap/2))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hmu.atTop_mul_const (half_pos hgap)) using 1
    funext n
    congr 1
    ring
  have hrhs : Tendsto (fun n => Real.exp (-(mu n*gap/2))*M^2+4*(eps n)^2*M^2) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] using
      (hexp.mul_const (M^2)).add (((heps.pow 2).const_mul 4).mul_const (M^2))
  have hb : ∀ᶠ n in atTop, ‖q n B‖^2 ≤ Real.exp (-(mu n*gap/2))*M^2+4*(eps n)^2*M^2 := by
    filter_upwards [hdata,hmu.eventually (eventually_gt_atTop 0),
      heps.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with n hn hmn hen
    have hab : a n ≤ B := by linarith [hn.1]
    have hd := spectralComplex_coupled_inward_decay (a n) B (mu n) (eps n) M hab hmn
      hn.2.1 hen.le hM (q n) (dq n) (w n) (alpha n) hn.2.2.1 hn.2.2.2.2.1
      hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1 hn.2.2.2.2.2.2.2
    have hi : Complex.normSq (q n (a n)) ≤ M^2 := by
      rw [← Complex.sq_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hn.2.2.2.1 2
    have he : Real.exp (-(mu n/2)*(B-a n)) ≤ Real.exp (-(mu n*gap/2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hn.1]
    rw [← Complex.sq_norm] at hd
    exact hd.trans (add_le_add
      ((mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_right he (sq_nonneg M))) le_rfl)
  have hs : Tendsto (fun n => ‖q n B‖^2) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun n => sq_nonneg _)) hb hrhs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using ht

end DefocusingNLS

end OAI
