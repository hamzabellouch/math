import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussLocalPositionCell

namespace OAI

/-! Fourth-order quadrature on a cube separated from an actual Coulomb pole. -/

noncomputable section
namespace ContinuumCoulomb

theorem translatedCoulomb_derivative_norm (k : ℕ) (y z : Position) :
    ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y-w)) z‖ =
      ‖iteratedFDeriv ℝ k Coulomb.coulombKernel (y-z)‖ := by
  let e : Position ≃ₗᵢ[ℝ] Position := LinearIsometryEquiv.neg ℝ
  have he := e.norm_iteratedFDeriv_comp_right (fun w => Coulomb.coulombKernel (y+w)) z k
  change ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y + -w)) z‖ =
    ‖iteratedFDeriv ℝ k (fun w => Coulomb.coulombKernel (y+w)) (-z)‖ at he
  rw [iteratedFDeriv_comp_add_left] at he
  simpa only [sub_eq_add_neg] using he

theorem coulomb_far_cell_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (y b : Position) (h r : ℝ), 0 ≤ h → 0 < r →
      (∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ v ∈ Set.Icc (-1:ℝ) 1,
        ∀ z ∈ Set.Icc (-1:ℝ) 1, r ≤ ‖y-cubePoint b (h/2) x v z‖) →
      |positionCellGauss b h (fun w => Coulomb.coulombKernel (y-w))-
        positionCellIntegral b h (fun w => Coulomb.coulombKernel (y-w))| ≤
        C*h^7/r^5 := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_derivative_decay
  refine ⟨C,hC,fun y b h r hh hr hdist => ?_⟩
  have hne (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) : y-cubePoint b (h/2) x v z ≠ 0 :=
    norm_pos_iff.mp (hr.trans_le (hdist x hx v hv z hz))
  have hD (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (v : ℝ) (hv : v ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedFDeriv ℝ 4 (fun w => Coulomb.coulombKernel (y-w))
        (cubePoint b (h/2) x v z)‖ ≤ C/r^5 := by
    rw [translatedCoulomb_derivative_norm]
    apply (le_div_iff₀ (pow_pos hr 5)).mpr
    have hp := hbound (4:Fin 5) _ (hne x hx v hv z hz)
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (hdist x hx v hv z hz) 5)
      (norm_nonneg _)).trans hp
  have he := positionCellGauss_error_local (fun w => Coulomb.coulombKernel (y-w)) b hh
    (div_nonneg (by linarith) (pow_nonneg hr.le 5))
    (fun x hx v hv z hz => (coulombKernel_contDiffAt (hne x hx v hv z hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4) |>.comp _
        (contDiffAt_const.sub contDiffAt_id)) hD
  apply he.trans_eq
  ring

end ContinuumCoulomb

end

end OAI
