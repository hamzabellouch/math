import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledBoundarySystem

namespace OAI

/-! A small two-channel Robin error preserves a strictly negative real
boundary form. The estimate permits either channel value to vanish. -/

namespace DefocusingNLS

private theorem real_boundary_bound (x y b : ℂ) :
    (star x*y).re ≤ b.re*‖x‖^2+‖x‖*‖y-b*x‖ := by
  have he : (star x*(b*x)).re = b.re*‖x‖^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.conj_re,
      Complex.conj_im,Complex.normSq_apply]
    ring
  have hr : star x*y = star x*(b*x)+star x*(y-b*x) := by ring
  rw [hr,Complex.add_re,he]
  exact add_le_add le_rfl ((Complex.re_le_norm (star x*(y-b*x))).trans_eq (by rw [norm_mul,norm_star]))

private theorem max_product_bound (x y : ℝ) :
    (x+y)*max x y ≤ 2*(x^2+y^2) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg (x-y),sq_nonneg x,sq_nonneg y]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (x-y),sq_nonneg x,sq_nonneg y]

theorem spectralCoupled_inward_boundary {R E A : ℝ}
    (Sp Sm : SpectralScalarBoundarySystem R E A) (hRE : R ≤ E)
    (c eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps ≤ c/4)
    (q : (ℂ × ℂ) × (ℂ × ℂ))
    (hp : ((Sp.U R).2/(Sp.U R).1).re ≤ -c*(Sp.k R)^2)
    (hm : ((Sm.U R).2/(Sm.U R).1).re ≤ -c*(Sm.k R)^2)
    (herr : spectralShellPairNorm (Sp.k R) (Sm.k R)
      (q-(Sp.extension q.1.1 R,Sm.extension q.2.1 R)) ≤
      eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) :
    (star q.1.1*q.1.2).re+(star q.2.1*q.2.2).re ≤
      -(c/2)*((Sp.k R*‖q.1.1‖)^2+(Sm.k R*‖q.2.1‖)^2) := by
  let x := Sp.k R*‖q.1.1‖
  let y := Sm.k R*‖q.2.1‖
  let M := max x y
  have hep : spectralShellNorm (Sp.k R) (q.1-Sp.extension q.1.1 R) ≤ eps*M :=
    (le_max_left _ _).trans herr
  have hem : spectralShellNorm (Sm.k R) (q.2-Sm.extension q.2.1 R) ≤ eps*M :=
    (le_max_right _ _).trans herr
  have hbp := Sp.inner_slope_bound hRE q.1 (eps*M) hep
  have hbm := Sm.inner_slope_bound hRE q.2 (eps*M) hem
  have hb1 := real_boundary_bound q.1.1 q.1.2 ((Sp.U R).2/(Sp.U R).1)
  have hb2 := real_boundary_bound q.2.1 q.2.2 ((Sm.U R).2/(Sm.U R).1)
  have h1 : (star q.1.1*q.1.2).re ≤ -c*x^2+eps*x*M := by
    calc
      _ ≤ _ := hb1
      _ ≤ (-c*(Sp.k R)^2)*‖q.1.1‖^2+‖q.1.1‖*(Sp.k R*(eps*M)) :=
        add_le_add (mul_le_mul_of_nonneg_right hp (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hbp (norm_nonneg _))
      _ = _ := by dsimp only [x]; ring
  have h2 : (star q.2.1*q.2.2).re ≤ -c*y^2+eps*y*M := by
    calc
      _ ≤ _ := hb2
      _ ≤ (-c*(Sm.k R)^2)*‖q.2.1‖^2+‖q.2.1‖*(Sm.k R*(eps*M)) :=
        add_le_add (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hbm (norm_nonneg _))
      _ = _ := by dsimp only [y]; ring
  have hmax := mul_le_mul_of_nonneg_left (max_product_bound x y) heps
  change eps*((x+y)*M) ≤ eps*(2*(x^2+y^2)) at hmax
  have hcoeff := mul_le_mul_of_nonneg_right hsmall (add_nonneg (sq_nonneg x) (sq_nonneg y))
  change _ ≤ -(c/2)*(x^2+y^2)
  nlinarith [sq_nonneg x,sq_nonneg y]

end DefocusingNLS

end OAI
