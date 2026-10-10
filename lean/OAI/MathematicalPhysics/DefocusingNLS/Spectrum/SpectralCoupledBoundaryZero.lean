import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledInwardBoundary

namespace OAI

/-! Nonnegative interior momentum and the inward outgoing boundary form
force the entire two-channel Cauchy state to vanish. -/

namespace DefocusingNLS

theorem spectralCoupled_boundary_zero {R E A : ℝ}
    (Sp Sm : SpectralScalarBoundarySystem R E A) (hRE : R ≤ E)
    (c eps : ℝ) (hc : 0 < c) (heps : 0 ≤ eps) (hsmall : eps ≤ c/4)
    (q : (ℂ × ℂ) × (ℂ × ℂ))
    (hp : ((Sp.U R).2/(Sp.U R).1).re ≤ -c*(Sp.k R)^2)
    (hm : ((Sm.U R).2/(Sm.U R).1).re ≤ -c*(Sm.k R)^2)
    (herr : spectralShellPairNorm (Sp.k R) (Sm.k R)
      (q-(Sp.extension q.1.1 R,Sm.extension q.2.1 R)) ≤
      eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖))
    (hflux : 0 ≤ (star q.1.1*q.1.2).re+(star q.2.1*q.2.2).re) : q = 0 := by
  have hb := spectralCoupled_inward_boundary Sp Sm hRE c eps heps hsmall q hp hm herr
  have hkp := Sp.positive_k R ⟨le_rfl,hRE⟩
  have hkm := Sm.positive_k R ⟨le_rfl,hRE⟩
  have hs : (Sp.k R*‖q.1.1‖)^2+(Sm.k R*‖q.2.1‖)^2 = 0 := by
    have hn := add_nonneg (sq_nonneg (Sp.k R*‖q.1.1‖)) (sq_nonneg (Sm.k R*‖q.2.1‖))
    nlinarith
  have hvp : q.1.1 = 0 := by
    have he : Sp.k R*‖q.1.1‖ = 0 := by nlinarith [sq_nonneg (Sm.k R*‖q.2.1‖)]
    exact norm_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hkp.ne')
  have hvm : q.2.1 = 0 := by
    have he : Sm.k R*‖q.2.1‖ = 0 := by nlinarith [sq_nonneg (Sp.k R*‖q.1.1‖)]
    exact norm_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hkm.ne')
  have hsp := Sp.inner_slope_bound hRE q.1
    (eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) ((le_max_left _ _).trans herr)
  have hsm := Sm.inner_slope_bound hRE q.2
    (eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) ((le_max_right _ _).trans herr)
  simp only [hvp,hvm,norm_zero,mul_zero,max_self,sub_zero] at hsp hsm
  exact Prod.ext (Prod.ext hvp (norm_eq_zero.mp (le_antisymm hsp (norm_nonneg _))))
    (Prod.ext hvm (norm_eq_zero.mp (le_antisymm hsm (norm_nonneg _))))

end DefocusingNLS

end OAI
