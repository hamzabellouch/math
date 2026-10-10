import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialNonvanishing

namespace OAI

/-! # Linear combinations and uniqueness for the coupled radial equation -/

open Set
open scoped ContDiff

namespace DefocusingNLS

private theorem deriv_sub_mul_c2 (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (c : ℂ) :
    deriv (fun r => f r - c * g r) = (fun r => deriv f r - c * deriv g r) ∧
    deriv (deriv (fun r => f r - c * g r)) =
      (fun r => deriv (deriv f) r - c * deriv (deriv g) r) := by
  have hd : deriv (fun r => f r - c * g r) =
      (fun r => deriv f r - c * deriv g r) := by
    funext r
    rw [deriv_fun_sub (hf.differentiable (by norm_num) r)
      ((hg.differentiable (by norm_num) r).const_mul c), deriv_const_mul_field]
  refine ⟨hd, ?_⟩
  rw [hd]
  funext r
  rw [deriv_fun_sub (hf.differentiable_deriv_two r)
    ((hg.differentiable_deriv_two r).const_mul c), deriv_const_mul_field]

theorem IsHarmonicRadialEigenpair.sub_mul {a b : ℝ} {m : ℕ} {Q : ℝ → ℂ}
    {η lam : ℂ} {f g u v : ℝ → ℂ}
    (hfg : IsHarmonicRadialEigenpair a b m Q η lam f g)
    (huv : IsHarmonicRadialEigenpair a b m Q η lam u v)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (c : ℂ) :
    IsHarmonicRadialEigenpair a b m Q η lam
      (fun r => f r - c * u r) (fun r => g r - c * v r) := by
  obtain ⟨hfu, hfuu⟩ := deriv_sub_mul_c2 f u hf hu c
  obtain ⟨hgv, hgvv⟩ := deriv_sub_mul_c2 g v hg hv c
  intro r hr
  obtain ⟨hf', hg'⟩ := hfg r hr
  obtain ⟨hu', hv'⟩ := huv r hr
  dsimp only
  rw [hfuu, hgvv, hfu, hgv]
  dsimp only
  constructor
  · linear_combination hf' - c * hu'
  · linear_combination hg' - c * hv'

theorem harmonicRadialEigenpair_eq_of_ball (a b : ℝ) (m : ℕ) (Q f g u v : ℝ → ℂ)
    (η lam : ℂ) (hQ : ContinuousOn Q (Ioi 0))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hfg : IsHarmonicRadialEigenpair a b m Q η lam f g)
    (huv : IsHarmonicRadialEigenpair a b m Q η lam u v)
    (R : ℝ) (hR : 0 < R) (c : ℂ)
    (he : ∀ r ∈ Ioc 0 R, f r = c * u r ∧ g r = c * v r) :
    ∀ r : ℝ, 0 < r → f r = c * u r ∧ g r = c * v r := by
  have hz := harmonicRadialEigenpair_zero_of_ball a b m Q
    (fun r => f r - c * u r) (fun r => g r - c * v r) η lam hQ
    (hf.sub (contDiff_const.mul hu)) (hg.sub (contDiff_const.mul hv))
    (hfg.sub_mul huv hf hg hu hv c) R hR (fun r hr =>
      ⟨sub_eq_zero.mpr (he r hr).1, sub_eq_zero.mpr (he r hr).2⟩)
  intro r hr
  exact ⟨sub_eq_zero.mp (hz r hr).1, sub_eq_zero.mp (hz r hr).2⟩

end DefocusingNLS

end OAI
