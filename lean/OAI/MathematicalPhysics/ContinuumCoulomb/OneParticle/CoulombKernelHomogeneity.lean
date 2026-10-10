import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombKernelSmooth
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Dilation

namespace OAI

/-! Derivatives through order four of the actual inverse-distance kernel
decay by the appropriate inverse power. -/

noncomputable section
open scoped ContDiff
namespace ContinuumCoulomb

theorem coulombKernel_iteratedFDeriv_scaling (k : ℕ) {c : ℝ} (hc : 0 < c)
    {x : Position} (hx : x ≠ 0) :
    c^k*‖iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x)‖ =
      c⁻¹*‖iteratedFDeriv ℝ k Coulomb.coulombKernel x‖ := by
  let e : Position ≃L[ℝ] Position := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have he (z : Position) : e z = c • z := rfl
  have hd := e.iteratedFDerivWithin_comp_right Coulomb.coulombKernel uniqueDiffOn_univ
    (Set.mem_univ (e x)) k
  simp only [Set.preimage_univ,iteratedFDerivWithin_univ] at hd
  have hright : iteratedFDeriv ℝ k (Coulomb.coulombKernel ∘ e) x =
      c^k • iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x) := by
    rw [hd]
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      smul_apply,ContinuousLinearEquiv.coe_coe,he]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (iteratedFDeriv ℝ k Coulomb.coulombKernel (c • x)).map_smul_univ (fun _ => c) v
  have hfun : Coulomb.coulombKernel ∘ e = c⁻¹ • Coulomb.coulombKernel := by
    funext z
    exact coulombKernel_smul z hc
  rw [hfun,iteratedFDeriv_const_smul_apply
    ((coulombKernel_contDiffAt hx).of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k).le : ContDiffAt ℝ k Coulomb.coulombKernel x)] at hright
  have hn := congrArg norm hright.symm
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos hc k),
    abs_of_pos (inv_pos.mpr hc)] using hn

theorem coulombKernel_derivative_decay :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : Fin 5, ∀ x : Position, x ≠ 0 →
      ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖*‖x‖^((k:ℕ)+1) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := coulombKernel_fixed_annulus_bounds
  refine ⟨C,hC,fun k x hx => ?_⟩
  let y : Position := ‖x‖⁻¹ • x
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖y‖ = 1 := by
    simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
    exact inv_mul_cancel₀ hn.ne'
  have hyne : y ≠ 0 := by intro he; simp only [he,norm_zero] at hy; norm_num at hy
  have hxy : ‖x‖ • y = x := by
    simp only [y,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have h := coulombKernel_iteratedFDeriv_scaling k hn hyne
  rw [hxy] at h
  have hb := hbound k y (by rw [hy]; norm_num) (by rw [hy]; norm_num)
  calc
    _ = ‖x‖*(‖x‖^(k:ℕ)*‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel x‖) := by ring
    _ = ‖x‖*(‖x‖⁻¹*‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel y‖) := by rw [h]
    _ = ‖iteratedFDeriv ℝ (k:ℕ) Coulomb.coulombKernel y‖ := by
      rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
    _ ≤ C := hb

end ContinuumCoulomb

end

end OAI
