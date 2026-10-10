import OAI.Analysis.KadisonSimilarity.OperatorAlgebra

namespace OAI

/-!
# Transfer through an isometric row

This is the operator calculation in the properly infinite case of
`prop:factor-representations`. The row/column derivation estimates must still be
provided before applying this lemma to a properly infinite von Neumann algebra.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Solving the three-term commutator expansion by compressing with an isometry. -/
theorem isometric_commutator_identity (Y : H →L[ℂ] H) (A X : K →L[ℂ] K)
    (V : K →L[ℂ] H) (hV : V.adjoint.comp V = ContinuousLinearMap.id ℂ K) :
    commutator A X =
      V.adjoint.comp ((commutator Y (V.comp (X.comp V.adjoint))).comp V) -
      V.adjoint.comp ((Y.comp V - V.comp A).comp X) -
      X.comp ((A.comp V.adjoint - V.adjoint.comp Y).comp V) := by
  simp only [commutator, mul_def, comp_sub, sub_comp, comp_assoc, hV, comp_id]
  simp only [← comp_assoc, hV, id_comp]
  abel

/-- The coefficient `1+2c` in the properly infinite factor estimate. -/
theorem norm_commutator_le_isometric_transfer (Y : H →L[ℂ] H)
    (A X : K →L[ℂ] K) (V : K →L[ℂ] H)
    (hV : V.adjoint.comp V = ContinuousLinearMap.id ℂ K)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hscalar : ‖commutator Y (V.comp (X.comp V.adjoint))‖ ≤
      δ * ‖V.comp (X.comp V.adjoint)‖)
    (hrow : ‖Y.comp V - V.comp A‖ ≤ c * δ)
    (hcol : ‖A.comp V.adjoint - V.adjoint.comp Y‖ ≤ c * δ) :
    ‖commutator A X‖ ≤ (1 + 2 * c) * δ * ‖X‖ := by
  have hVnorm : ‖V‖ ≤ 1 := by
    have h := norm_adjoint_comp_self V
    rw [hV] at h
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := K)
    nlinarith [norm_nonneg V]
  have hVadj : ‖V.adjoint‖ ≤ 1 := by simpa using hVnorm
  have hmiddle : ‖V.comp (X.comp V.adjoint)‖ ≤ ‖X‖ := by
    calc
      _ ≤ ‖V‖ * (‖X‖ * ‖V.adjoint‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖X‖ * 1) := by gcongr
      _ = ‖X‖ := by ring
  have hfirst :
      ‖V.adjoint.comp ((commutator Y (V.comp (X.comp V.adjoint))).comp V)‖ ≤
        δ * ‖X‖ := by
    calc
      _ ≤ ‖V.adjoint‖ * (‖commutator Y (V.comp (X.comp V.adjoint))‖ * ‖V‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * ((δ * ‖X‖) * 1) := by
        gcongr
        exact hscalar.trans (mul_le_mul_of_nonneg_left hmiddle hδ)
      _ = δ * ‖X‖ := by ring
  have hsecond : ‖V.adjoint.comp ((Y.comp V - V.comp A).comp X)‖ ≤ c * δ * ‖X‖ := by
    calc
      _ ≤ ‖V.adjoint‖ * (‖Y.comp V - V.comp A‖ * ‖X‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * ((c * δ) * ‖X‖) := by gcongr
      _ = c * δ * ‖X‖ := by ring
  have hthird : ‖X.comp ((A.comp V.adjoint - V.adjoint.comp Y).comp V)‖ ≤ c * δ * ‖X‖ := by
    calc
      _ ≤ ‖X‖ * (‖A.comp V.adjoint - V.adjoint.comp Y‖ * ‖V‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖X‖ * ((c * δ) * 1) := by gcongr
      _ = c * δ * ‖X‖ := by ring
  rw [isometric_commutator_identity Y A X V hV]
  calc
    _ ≤ (‖V.adjoint.comp ((commutator Y (V.comp (X.comp V.adjoint))).comp V)‖ +
        ‖V.adjoint.comp ((Y.comp V - V.comp A).comp X)‖) +
        ‖X.comp ((A.comp V.adjoint - V.adjoint.comp Y).comp V)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (δ * ‖X‖ + c * δ * ‖X‖) + c * δ * ‖X‖ :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = (1 + 2 * c) * δ * ‖X‖ := by ring

end KadisonSimilarity

end

end OAI
