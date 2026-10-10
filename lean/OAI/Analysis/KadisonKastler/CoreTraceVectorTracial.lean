import OAI.Analysis.KadisonKastler.CoreTraceSymmetryProduct

namespace OAI

/-! # The vector trace determined by conjugation symmetry

Two operators satisfying the same Tomita vector identity have cyclic
vector coefficients. This supplies the trace identity on the frequency
corner without a polarization argument or an assumed trace.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coreTraceSymmetry_tracial (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : Function.Involutive C) (ξ : H) (A B : H →L[ℂ] H)
    (hA : A ∈ coreTraceSymmetrySpace C ξ)
    (hB : B ∈ coreTraceSymmetrySpace C ξ) :
    inner ℂ ξ ((A * B) ξ) = inner ℂ ξ ((B * A) ξ) := by
  have ha := coreTraceSymmetry_vector C hC ξ A hA
  have hb := coreTraceSymmetry_vector C hC ξ B hB
  have hca : C (A ξ) = (star A) ξ := by rw [ha, hC]
  calc
    inner ℂ ξ ((A * B) ξ) = inner ℂ ((star A) ξ) (B ξ) := by
      simpa only [mul_apply_eq_comp, ← ContinuousLinearMap.star_eq_adjoint, star_star] using
        (ContinuousLinearMap.adjoint_inner_right (star A) ξ (B ξ))
    _ = inner ℂ (C (A ξ)) (C ((star B) ξ)) := by rw [hca, ← hb]
    _ = inner ℂ ((star B) ξ) (A ξ) := by
      rw [conjugateIsometry_inner]
      exact inner_conj_symm _ _
    _ = inner ℂ ξ ((B * A) ξ) := by
      simpa only [mul_apply_eq_comp, ← ContinuousLinearMap.star_eq_adjoint, star_star] using
        (ContinuousLinearMap.adjoint_inner_right (star B) ξ (A ξ)).symm

end

end KadisonKastler

end OAI
