import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoupledBoundarySystem

namespace OAI

/-! The coupled Green error gives both local Robin errors, including when
one of the channel values is zero. -/

open Set
namespace DefocusingNLS

theorem spectralCoupled_inner_robin_bound {R E A : ℝ}
    (Sp Sm : SpectralScalarBoundarySystem R E A) (hRE : R ≤ E)
    (q : (ℂ × ℂ) × (ℂ × ℂ)) (eps : ℝ)
    (herr : spectralShellPairNorm (Sp.k R) (Sm.k R)
      (q-(Sp.extension q.1.1 R,Sm.extension q.2.1 R)) ≤
      eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) :
    ‖q.1.2-((Sp.U R).2/(Sp.U R).1)*q.1.1‖ ≤
      Sp.k R*(eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) ∧
    ‖q.2.2-((Sm.U R).2/(Sm.U R).1)*q.2.1‖ ≤
      Sm.k R*(eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) := by
  constructor
  · apply Sp.inner_slope_bound hRE q.1
    exact (le_max_left _ _).trans herr
  · apply Sm.inner_slope_bound hRE q.2
    exact (le_max_right _ _).trans herr

theorem spectralCoupled_inner_robin_scaled {R E A : ℝ}
    (Sp Sm : SpectralScalarBoundarySystem R E A) (hRE : R ≤ E)
    (q : (ℂ × ℂ) × (ℂ × ℂ)) (eps C : ℝ) (heps : 0 ≤ eps)
    (hp : (Sp.k R)^2 ≤ C) (hm : (Sm.k R)^2 ≤ C)
    (herr : spectralShellPairNorm (Sp.k R) (Sm.k R)
      (q-(Sp.extension q.1.1 R,Sm.extension q.2.1 R)) ≤
      eps*max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖)) :
    ‖q.1.2-((Sp.U R).2/(Sp.U R).1)*q.1.1‖ ≤ eps*C*(‖q.1.1‖+‖q.2.1‖) ∧
    ‖q.2.2-((Sm.U R).2/(Sm.U R).1)*q.2.1‖ ≤ eps*C*(‖q.1.1‖+‖q.2.1‖) := by
  have hkp := (Sp.positive_k R ⟨le_rfl,hRE⟩).le
  have hkm := (Sm.positive_k R ⟨le_rfl,hRE⟩).le
  have hc : Sp.k R*Sm.k R ≤ C := by nlinarith [sq_nonneg (Sp.k R-Sm.k R)]
  have hmax : max (Sp.k R*‖q.1.1‖) (Sm.k R*‖q.2.1‖) ≤
      Sp.k R*‖q.1.1‖+Sm.k R*‖q.2.1‖ :=
    max_le (le_add_of_nonneg_right (mul_nonneg hkm (norm_nonneg _)))
      (le_add_of_nonneg_left (mul_nonneg hkp (norm_nonneg _)))
  have hb := spectralCoupled_inner_robin_bound Sp Sm hRE q eps herr
  constructor
  · apply hb.1.trans
    calc
      _ ≤ Sp.k R*(eps*(Sp.k R*‖q.1.1‖+Sm.k R*‖q.2.1‖)) := by gcongr
      _ = eps*((Sp.k R)^2*‖q.1.1‖+(Sp.k R*Sm.k R)*‖q.2.1‖) := by ring
      _ ≤ eps*(C*‖q.1.1‖+C*‖q.2.1‖) := by gcongr
      _ = _ := by ring
  · apply hb.2.trans
    calc
      _ ≤ Sm.k R*(eps*(Sp.k R*‖q.1.1‖+Sm.k R*‖q.2.1‖)) := by gcongr
      _ = eps*((Sp.k R*Sm.k R)*‖q.1.1‖+(Sm.k R)^2*‖q.2.1‖) := by ring
      _ ≤ eps*(C*‖q.1.1‖+C*‖q.2.1‖) := by gcongr
      _ = _ := by ring

end DefocusingNLS

end OAI
