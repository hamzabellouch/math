import OAI.Analysis.PlanarPacking.MatrixL1

namespace OAI

namespace SharpPlanar
section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def certifiedEquiv (A W : E →L[ℝ] E) (h : ‖1-W*A‖ < 1) : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective A.toLinearMap (approximate_inverse_bijective A W h)).toContinuousLinearEquiv
lemma certifiedEquiv_apply (A W : E →L[ℝ] E) (h : ‖1-W*A‖ < 1) (x : E) :
    certifiedEquiv A W h x = A x := rfl

lemma certified_inverse_norm_le (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap‖ ≤ ‖W‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm x) = x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply x
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm x‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm x))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W x‖/(1-δ) := by rw [he]
    _ ≤ (‖W‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right (W.le_opNorm x) hd0.le
    _ = (‖W‖/(1-δ))*‖x‖ := by ring

lemma certified_inverse_comp_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A W : E →L[ℝ] E) (U : F →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖((certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap).comp U‖ ≤
      ‖W.comp U‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)) = U x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply _
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm (U x)‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm (U x)))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W (U x)‖/(1-δ) := by rw [he]
    _ ≤ (‖W.comp U‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right ((W.comp U).le_opNorm x) hd0.le
    _ = (‖W.comp U‖/(1-δ))*‖x‖ := by ring
end Inverse
end SharpPlanar

end OAI
