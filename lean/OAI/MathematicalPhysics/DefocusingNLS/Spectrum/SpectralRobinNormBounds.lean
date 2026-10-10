import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledBoundarySystem

namespace OAI

/-! Norm bounds and coercivity of the local diagonal Robin relation. -/

open Set
namespace DefocusingNLS

theorem SpectralScalarBoundarySystem.inner_slope_norm {R E A : ℝ}
    (S : SpectralScalarBoundarySystem R E A) (hRE : R ≤ E) (J : ℝ)
    (hext : ∀ z : ℂ, ∀ r ∈ Icc R E,
      spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k R*‖z‖) :
    ‖(S.U R).2/(S.U R).1‖ ≤ J*(S.k R)^2 := by
  have hk := S.positive_k R ⟨le_rfl,hRE⟩
  have hs := spectralShellNorm_slope (S.k R) hk (S.extension 1 R)
  have he := hext 1 R ⟨le_rfl,hRE⟩
  have hid : (S.extension 1 R).2 = (S.U R).2/(S.U R).1 := by
    simp only [SpectralScalarBoundarySystem.extension,Prod.smul_snd,smul_eq_mul]
    ring
  rw [hid] at hs
  simp only [norm_one,mul_one] at he
  exact (hs.trans (mul_le_mul_of_nonneg_left he hk.le)).trans_eq (by ring)

theorem spectralCoupled_robin_coercivity (z w dz dw alpha beta : ℂ) (mu eps : ℝ)
    (hmu : 0 ≤ mu) (_heps : 0 ≤ eps) (hsmall : eps ≤ 1/4)
    (ha : mu ≤ ‖alpha‖) (hb : mu ≤ ‖beta‖)
    (hza : ‖dz-alpha*z‖ ≤ eps*mu*(‖z‖+‖w‖))
    (hwb : ‖dw-beta*w‖ ≤ eps*mu*(‖z‖+‖w‖)) :
    mu*(‖z‖+‖w‖) ≤ 2*(‖dz‖+‖dw‖) := by
  have h1 : mu*‖z‖ ≤ ‖dz‖+eps*mu*(‖z‖+‖w‖) := by
    calc
      _ ≤ ‖alpha‖*‖z‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ = ‖alpha*z‖ := (norm_mul _ _).symm
      _ = ‖dz-(dz-alpha*z)‖ := by congr 1; ring
      _ ≤ ‖dz‖+‖dz-alpha*z‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hza
  have h2 : mu*‖w‖ ≤ ‖dw‖+eps*mu*(‖z‖+‖w‖) := by
    calc
      _ ≤ ‖beta‖*‖w‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = ‖beta*w‖ := (norm_mul _ _).symm
      _ = ‖dw-(dw-beta*w)‖ := by congr 1; ring
      _ ≤ ‖dw‖+‖dw-beta*w‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hwb
  have hab := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hmu (add_nonneg (norm_nonneg z) (norm_nonneg w)))
  nlinarith only [h1,h2,hab]

end DefocusingNLS

end OAI
