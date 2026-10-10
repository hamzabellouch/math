import OAI.NumberTheory.Ostmann.Conclusion.ActualCovariance

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Conclusion
open Construction

theorem complex_pair_re_le_half_energy (z w : ℂ) :
    2*(z*conj w).re ≤ ‖z‖^2+‖w‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (z.re-w.re), sq_nonneg (z.im-w.im)]

theorem prior_permuted_self_covariance {J S Γ : Type*} [Fintype J] [Fintype S]
    (μ : FinitePrior J) (F : J → S → ℂ) (e : Γ → J ≃ J)
    (he : ∀ a x, μ.mass (e a x)=μ.mass x) (a : Γ) :
    pairCovariance (fun y : J × S => μ.mass y.1)
      (fun a y => F (e a y.1) y.2) a a =
        μ.mean (fun x => ∑s, ‖F x s‖^2) := by
  have h := (e a).sum_comp (fun x => μ.mass x * ∑s, ‖F x s‖^2)
  simpa only [pairCovariance, Fintype.sum_prod_type, ← Finset.mul_sum,
    Complex.mul_conj, Complex.ofReal_re, ← Complex.sq_norm, he, FinitePrior.mean] using h

theorem prior_permuted_covariance_le_energy {J S Γ : Type*} [Fintype J] [Fintype S]
    (μ : FinitePrior J) (F : J → S → ℂ) (e : Γ → J ≃ J)
    (he : ∀ a x, μ.mass (e a x)=μ.mass x) (a b : Γ) :
    pairCovariance (fun y : J × S => μ.mass y.1)
      (fun a y => F (e a y.1) y.2) a b ≤
        μ.mean (fun x => ∑s, ‖F x s‖^2) := by
  have ha := prior_permuted_self_covariance μ F e he a
  have hb := prior_permuted_self_covariance μ F e he b
  have h : 2 * pairCovariance (fun y : J × S => μ.mass y.1)
      (fun a y => F (e a y.1) y.2) a b ≤
      pairCovariance (fun y : J × S => μ.mass y.1)
        (fun a y => F (e a y.1) y.2) a a +
      pairCovariance (fun y : J × S => μ.mass y.1)
        (fun a y => F (e a y.1) y.2) b b := by
    unfold pairCovariance
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y hy
    have hp := mul_le_mul_of_nonneg_left
      (complex_pair_re_le_half_energy (F (e a y.1) y.2) (F (e b y.1) y.2))
      (μ.mass_nonneg y.1)
    simpa only [Complex.mul_conj, Complex.ofReal_re, ← Complex.sq_norm,
      mul_add, mul_left_comm] using hp
  rw [ha,hb] at h
  linarith

end Ostmann.Conclusion

end

end OAI
