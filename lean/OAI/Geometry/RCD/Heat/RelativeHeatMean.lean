import OAI.Geometry.RCD.Heat.UniformHeatMeanComparison

namespace OAI

/-! # Converting the relative heat comparison to quadratic-form order -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The norm estimate in an exact mean frame is precisely the relative
quadratic comparison in the original, possibly ill-conditioned coordinates. -/
theorem relative_heat_mean_of_conjugated_norm
    (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (U : E →L[ℝ] SobolevSpace μ hQ) (s : Set X) (hs : MeasurableSet s)
    (A : E ≃L[ℝ] E) (hA : IsExactMeanNormalization μ hQ U s hs A)
    (Q : E →L[ℝ] E) {η : ℝ}
    (hclose : ‖(A : E →L[ℝ] E).adjoint.comp (Q.comp (A : E →L[ℝ] E)) -
      ContinuousLinearMap.id ℝ E‖ ≤ η) (v : E) :
    (1 - η) * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤ ⟪v, Q v⟫_ℝ ∧
      ⟪v, Q v⟫_ℝ ≤ (1 + η) * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ := by
  let D := (A : E →L[ℝ] E).adjoint.comp (Q.comp (A : E →L[ℝ] E)) -
    ContinuousLinearMap.id ℝ E
  let w := A.symm v
  have hnorm := meanGram_energy_of_exact_normalization μ hQ U s hs A hA v
  have hb : |⟪w, D w⟫_ℝ| ≤ η * ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖w‖ * ‖D w‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖w‖ * (η * ‖w‖) := mul_le_mul_of_nonneg_left
        ((D.le_opNorm w).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg w)))
        (norm_nonneg w)
      _ = _ := by ring
  have he : ⟪w, D w⟫_ℝ = ⟪v, Q v⟫_ℝ - ‖w‖ ^ 2 := by
    dsimp only [D]
    rw [sub_apply, inner_sub_right, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply]
    simp only [w, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  rw [he] at hb
  change ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ = ‖w‖ ^ 2 at hnorm
  rw [hnorm]
  exact ⟨by nlinarith [(abs_le.mp hb).1], by nlinarith [(abs_le.mp hb).2]⟩

end RegularPointCoordinates

end

end OAI
