import Mathlib

namespace OAI

noncomputable section
open Module

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

def mixedOperator (B : F →L[ℝ] E →L[ℝ] ℝ) : F →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

omit [CompleteSpace F] in
@[simp] lemma mixedOperator_inner (B : F →L[ℝ] E →L[ℝ] ℝ) (v : F) (w : E) :
    inner ℝ (mixedOperator B v) w=B v w :=
  InnerProductSpace.toDual_symm_apply

omit [CompleteSpace F] in
lemma mixedOperator_norm_le (B : F →L[ℝ] E →L[ℝ] ℝ) {a : ℝ}
    (ha : 0≤a) (hB : ∀ v w, |B v w|≤a*‖v‖*‖w‖) :
    ‖mixedOperator B‖≤a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro v
  have he : ‖mixedOperator B v‖=‖B v‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map (B v)
  rw [he]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg ha (norm_nonneg v))
  intro w
  simpa only [Real.norm_eq_abs] using hB v w

lemma mixed_factor_adjoint {D : E →L[ℝ] E} {J : E →L[ℝ] F}
    {P : F →L[ℝ] E} (hD : D.toLinearMap.IsSymmetric)
    (hfactor : ∀ v w, inner ℝ (D v) w=inner ℝ (P (J v)) w) :
    D=J.adjoint.comp P.adjoint := by
  ext v
  apply ext_inner_right ℝ
  intro w
  calc
    inner ℝ (D v) w=inner ℝ v (D w) := hD _ _
    _=inner ℝ (D w) v := real_inner_comm _ _
    _=inner ℝ (P (J w)) v := hfactor _ _
    _=inner ℝ (J w) (P.adjoint v) := by
      rw [P.adjoint_inner_right]
    _=inner ℝ (J.adjoint (P.adjoint v)) w := by
      rw [J.adjoint_inner_left,real_inner_comm]
    _=inner ℝ ((J.adjoint.comp P.adjoint) v) w := rfl

omit [CompleteSpace E] [CompleteSpace F] in
lemma factor_surjective_of_right_inverse [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {D S : E →L[ℝ] E} {J : F →L[ℝ] E} {C : E →L[ℝ] F}
    (hdim : finrank ℝ E=finrank ℝ F)
    (hDS : ∀ v, D (S v)=v) (hD : ∀ v, D v=J (C v)) :
    Function.Surjective C := by
  have hDin : Function.Injective D := D.toLinearMap.injective_iff_surjective.mpr
    (fun v => ⟨S v,hDS v⟩)
  have hCin : Function.Injective C := by
    intro v w hvw
    apply hDin
    rw [hD,hD,hvw]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := C.toLinearMap)).mp hCin

end WeakMTWTransport

end

end OAI
