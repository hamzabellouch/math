import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnSlopeLimit

namespace OAI

/-! The explicit no-turn errors decrease when the inner radius increases. -/

namespace DefocusingNLS

theorem spectralNoTurn_derivative_radius_mono (C R L : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRL : R ≤ L) :
    2/L+4*C/L^3 ≤ 2/R+4*C/R^3 := by
  have h1 : 2/L ≤ 2/R := div_le_div_of_nonneg_left (by norm_num) hR hRL
  have h2 : 4*C/L^3 ≤ 4*C/R^3 := div_le_div_of_nonneg_left (by positivity)
    (by positivity) (pow_le_pow_left₀ hR.le hRL 3)
  exact add_le_add h1 h2

theorem spectralNoTurn_residual_radius_mono (C R L omega : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRL : R ≤ L) :
    spectralNoTurnResidualBound C L omega ≤ spectralNoTurnResidualBound C R omega := by
  have h1 := spectralNoTurn_derivative_radius_mono C R L hC hR hRL
  have h2 : 3/(4*L) ≤ 3/(4*R) := div_le_div_of_nonneg_left (by norm_num)
    (by positivity) (by linarith)
  unfold spectralNoTurnResidualBound
  exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

theorem spectralNoTurn_branch_radius_mono (C R L omega E : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRL : R ≤ L) :
    spectralNoTurnBranchError C L omega E ≤ spectralNoTurnBranchError C R omega E := by
  have hL : 0 < L := hR.trans_le hRL
  have hJ := spectralNoTurn_residual_radius_mono C R L omega hC hR hRL
  have hJL : 0 ≤ spectralNoTurnResidualBound C L omega := by
    unfold spectralNoTurnResidualBound
    positivity
  unfold spectralNoTurnBranchError
  dsimp only
  gcongr

theorem spectralNoTurn_real_radius_mono (C R L omega E : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRL : R ≤ L) :
    spectralNoTurnRealError C L omega E ≤ spectralNoTurnRealError C R omega E := by
  have h1 := spectralNoTurn_derivative_radius_mono C R L hC hR hRL
  have h2 := spectralNoTurn_branch_radius_mono C R L omega E hC hR hRL
  unfold spectralNoTurnRealError
  gcongr

end DefocusingNLS

end OAI
