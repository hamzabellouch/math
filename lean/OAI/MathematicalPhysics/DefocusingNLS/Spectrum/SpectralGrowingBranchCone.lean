import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBranchCone

namespace OAI

/-! A controlled residual and an exponentially smaller second branch leave
the actual Cauchy data in the growing branch's Robin cone. -/

namespace DefocusingNLS

theorem spectralGrowingBranch_error (k C H N eps : ℝ) (hk : 0 < k)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (a b : ℂ) (D U q : ℂ × ℂ)
    (hU : spectralShellNorm k U ≤ C*Real.exp (-H))
    (hb : ‖b‖ ≤ C/2*N)
    (herr : spectralShellNorm k (q-(a • D+b • U)) ≤ eps*Real.exp H*N) :
    spectralShellNorm k (q-a • D) ≤
      (eps+C^2/2*Real.exp (-2*H))*Real.exp H*N := by
  have heq : q-a • D = (q-(a • D+b • U))+b • U := by abel
  have hexp : Real.exp (-2*H)*Real.exp H = Real.exp (-H) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ spectralShellNorm k (q-(a • D+b • U))+spectralShellNorm k (b • U) := by
      rw [heq]
      exact spectralShellNorm_add_le k hk.le _ _
    _ ≤ eps*Real.exp H*N+(C/2*N)*(C*Real.exp (-H)) := by
      rw [spectralShellNorm_smul]
      exact add_le_add herr (mul_le_mul hb hU
        (spectralShellNorm_nonneg k hk.le _) (by positivity))
    _ = _ := by
      rw [add_mul,add_mul]
      have hh : C^2/2*Real.exp (-2*H)*Real.exp H*N = C^2/2*Real.exp (-H)*N := by
        rw [mul_assoc (C^2/2),hexp]
      rw [hh]
      ring

theorem spectralGrowingBranch_cone (k H N theta : ℝ) (hk : 0 < k) (hN : 0 < N)
    (htheta : theta ≤ 1/64) (a L : ℂ) (D q : ℂ × ℂ)
    (hD : D.2 = L*D.1) (hvalue : k*‖D.1‖ = Real.exp H)
    (hL : ‖L‖ ≤ (3/2 : ℝ)*k^2) (ha : N/8 ≤ ‖a‖)
    (hclose : spectralShellNorm k (q-a • D) ≤ theta*Real.exp H*N) :
    q.1 ≠ 0 ∧ ‖q.2-L*q.1‖ ≤ (1/2 : ℝ)*k^2*‖q.1‖ := by
  have hmass : 0 < Real.exp H*N := mul_pos (Real.exp_pos H) hN
  have htheta0 : 0 ≤ theta := by
    have hn := (spectralShellNorm_nonneg k hk.le _).trans hclose
    nlinarith
  obtain ⟨hv,hr⟩ := spectralBranch_value_residual k (3/2) (Real.exp H)
    (theta*Real.exp H*N) hk (by norm_num) a L D q hD hvalue hL hclose
  have ha' : (1/8 : ℝ)*(Real.exp H*N) ≤ ‖a‖*Real.exp H := by
    have hh := mul_le_mul_of_nonneg_right ha (Real.exp_pos H).le
    nlinarith
  have hval : (1/8-theta)*(Real.exp H*N) ≤ k*‖q.1‖ := by nlinarith
  have hvalpos : 0 < k*‖q.1‖ := lt_of_lt_of_le (mul_pos (by linarith) hmass) hval
  refine ⟨norm_pos_iff.mp (by nlinarith),hr.trans ?_⟩
  have hc : (5/2 : ℝ)*theta ≤ (1/2)*(1/8-theta) := by linarith
  have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hk.le hmass.le)
  have hv' := mul_le_mul_of_nonneg_left hval (by positivity : 0 ≤ (1/2 : ℝ)*k)
  nlinarith

theorem spectralGrowingBranch_relative_cone (k H N theta : ℝ) (hk : 0 < k) (hN : 0 < N)
    (eps : ℝ) (heps : 0 < eps) (htheta : theta ≤ min (1/16) (eps/40)) (a L : ℂ) (D q : ℂ × ℂ)
    (hD : D.2 = L*D.1) (hvalue : k*‖D.1‖ = Real.exp H)
    (hL : ‖L‖ ≤ (3/2 : ℝ)*k^2) (ha : N/8 ≤ ‖a‖)
    (hclose : spectralShellNorm k (q-a • D) ≤ theta*Real.exp H*N) :
    q.1 ≠ 0 ∧ ‖q.2-L*q.1‖ ≤ eps*k^2*‖q.1‖ := by
  have hmass : 0 < Real.exp H*N := mul_pos (Real.exp_pos H) hN
  have htheta0 : 0 ≤ theta := by
    have hn := (spectralShellNorm_nonneg k hk.le _).trans hclose
    nlinarith
  obtain ⟨hv,hr⟩ := spectralBranch_value_residual k (3/2) (Real.exp H)
    (theta*Real.exp H*N) hk (by norm_num) a L D q hD hvalue hL hclose
  have ha' : (1/8 : ℝ)*(Real.exp H*N) ≤ ‖a‖*Real.exp H := by
    have hh := mul_le_mul_of_nonneg_right ha (Real.exp_pos H).le
    nlinarith
  have hval : (1/8-theta)*(Real.exp H*N) ≤ k*‖q.1‖ := by nlinarith
  have hsmall := (le_min_iff.mp htheta).1
  have hepssmall := (le_min_iff.mp htheta).2
  have hvalpos : 0 < k*‖q.1‖ := lt_of_lt_of_le (mul_pos (by linarith) hmass) hval
  refine ⟨norm_pos_iff.mp (by nlinarith),hr.trans ?_⟩
  have hc : (5/2 : ℝ)*theta ≤ eps*(1/8-theta) := by
    have hgap : (1/16 : ℝ) ≤ 1/8-theta := by linarith
    have hm := mul_le_mul_of_nonneg_left hgap heps.le
    linarith
  have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hk.le hmass.le)
  have hv' := mul_le_mul_of_nonneg_left hval (by positivity : 0 ≤ eps*k)
  nlinarith


theorem spectralGrowingBranch_value_lower (k H N theta : ℝ) (hk : 0 < k)
    (hN : 0 ≤ N) (htheta : theta ≤ 1/16) (a : ℂ) (D q : ℂ × ℂ)
    (hvalue : k*‖D.1‖ = Real.exp H) (ha : N/8 ≤ ‖a‖)
    (hclose : spectralShellNorm k (q-a • D) ≤ theta*Real.exp H*N) :
    (1/16 : ℝ)*Real.exp H*N ≤ k*‖q.1‖ := by
  let e := q-a • D
  have hsmall : k*‖e.1‖ ≤ theta*Real.exp H*N := by
    calc
      _ ≤ spectralShellNorm k e := le_add_of_nonneg_right (by
        exact mul_nonneg (inv_nonneg.mpr hk.le) (norm_nonneg _))
      _ ≤ _ := hclose
  have he : a*D.1 = q.1-e.1 := by
    dsimp only [e,Prod.fst_sub,Prod.smul_fst,smul_eq_mul]
    ring
  have htriangle := mul_le_mul_of_nonneg_left (norm_sub_le q.1 e.1) hk.le
  rw [← he,norm_mul] at htriangle
  have hlow := mul_le_mul_of_nonneg_right ha (Real.exp_pos H).le
  have hmass : 0 ≤ Real.exp H*N := mul_nonneg (Real.exp_pos H).le hN
  have hthetaN := mul_le_mul_of_nonneg_right htheta hmass
  nlinarith

end DefocusingNLS

end OAI
