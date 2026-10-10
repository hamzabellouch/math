import OAI.Geometry.NodalSets.Elliptic.StereographicSecondDerivative

namespace OAI

namespace Yau.Target
open scoped ContDiff RealInnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma stereoInvFunAux_second_at (v x w u : E) :
    fderiv ℝ (fun z ↦ fderiv ℝ (stereoInvFunAux v) z w) x u =
      (8 * stereoReciprocal x^3 * ⟪x,u⟫ * ⟪x,w⟫ -
        2 * stereoReciprocal x^2 * ⟪u,w⟫) • stereoNumerator v x +
      (-2 * stereoReciprocal x^2 * ⟪x,w⟫) • ((4:ℝ) • u + (2*⟪x,u⟫) • v) +
      (-2 * stereoReciprocal x^2 * ⟪x,u⟫) • ((4:ℝ) • w + (2*⟪x,w⟫) • v) +
      (2 * stereoReciprocal x * ⟪u,w⟫) • v := by
  simp_rw [stereoInvFunAux_fderiv]
  have hb : HasFDerivAt (fun z : E ↦ ⟪z,w⟫) (innerSL ℝ w) x := by
    convert! (innerSL ℝ w).hasFDerivAt (x := x) using 1
    funext z
    exact (real_inner_comm z w).symm
  have hA := (((stereoReciprocal_hasFDerivAt x).pow 2).const_mul (-2:ℝ)).mul hb
  have hB := (hasFDerivAt_const ((4:ℝ) • w) x).add ((hb.const_mul (2:ℝ)).smul_const v)
  have hd := (hA.smul (stereoNumerator_hasFDerivAt v x)).add
    ((stereoReciprocal_hasFDerivAt x).smul hB)
  change HasFDerivAt (fun z : E ↦
    (-2 * stereoReciprocal z^2 * ⟪z,w⟫) • stereoNumerator v z +
      stereoReciprocal z • ((4:ℝ) • w + (2*⟪z,w⟫) • v)) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_eq_mul,
    Pi.mul_apply,Pi.add_apply,zero_add,real_inner_comm w u,show (2:ℕ)-1=1 from rfl,pow_one]
  module

lemma stereoInvFunAux_second_fderiv_at (v x w u : E) :
    fderiv ℝ (fderiv ℝ (stereoInvFunAux v)) x u w =
      fderiv ℝ (fun z ↦ fderiv ℝ (stereoInvFunAux v) z w) x u := by
  have hd := (contDiff_stereoInvFunAux (v := v) (m := ∞)).fderiv_right
    (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)
  have he := (hd.differentiable (by simp) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  simpa using (congrArg (fun L : E →L[ℝ] E ↦ L u) he.fderiv).symm

end
end Yau.Target

end OAI
