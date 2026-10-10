import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowJacobianVariation

namespace OAI

/-! Gronwall's bound for the first spatial derivative of the actual flow. -/

noncomputable section
open Set
open scoped ContDiff
namespace ContinuumCoulomb

theorem flow_first_derivative_bound_along {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (B : ℝ) (hB : 0 ≤ B) (x : Position)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖fderiv ℝ (v t) (G x t)‖ ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖fderiv ℝ (fun y => G y t) x‖ ≤ Real.exp B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos B).le
  intro e
  let u : ℝ → Position := fun s => fderiv ℝ (fun y => G y s) x e
  let du : ℝ → Position := fun s => fderiv ℝ (v s) (G x s) (u s)
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt u (du s) (Icc (0:ℝ) 1) s :=
    flow_spatial_variational hU hslab v hv G hG x e s hs
  have hright (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt u (du s) (Ici s) s := by
    apply (hd s ⟨hs.1,hs.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
  have hu0 : u 0 = e := by
    have hzero : (fun y => G y 0) = id := funext hG.1
    change fderiv ℝ (fun y => G y 0) x e = e
    rw [hzero,fderiv_id]
    rfl
  have hdu (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : ‖du s‖ ≤ B * ‖u s‖ + 0 := by
    exact ((fderiv ℝ (v s) (G x s)).le_opNorm (u s)).trans
      (by simpa only [add_zero] using
        mul_le_mul_of_nonneg_right (hbound s ⟨hs.1,hs.2.le⟩) (norm_nonneg (u s)))
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivWithinAt.continuousOn hd) hright
    (show ‖u 0‖ ≤ ‖e‖ by rw [hu0]) hdu t ht
  simp only [gronwallBound_ε0,sub_zero] at h
  have he : Real.exp (B*t) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (by nlinarith [ht.2])
  exact h.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (norm_nonneg e))

theorem flow_first_derivative_bound {U : Set (ℝ × Position)} (hU : IsOpen U)
    (hslab : Icc (0:ℝ) 1 ×ˢ (univ : Set Position) ⊆ U)
    (v : ℝ → Position → Position)
    (hv : ContDiffOn ℝ 4 (fun p : ℝ × Position => v p.1 p.2) U)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow v G)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, ‖fderiv ℝ (v t) x‖ ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : Position) :
    ‖fderiv ℝ (fun y => G y t) x‖ ≤ Real.exp B :=
  flow_first_derivative_bound_along hU hslab v hv G hG B hB x
    (fun s hs => hbound s hs (G x s)) t ht

end ContinuumCoulomb

end

end OAI
