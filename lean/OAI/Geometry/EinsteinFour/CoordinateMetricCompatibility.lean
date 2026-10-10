import OAI.Geometry.EinsteinFour.ActualRicciContraction

namespace OAI

/-! The metric-compatibility identity for the actual Christoffel formula.
This algebraic step needs only invertibility of the chart metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

private theorem matrix_lower_inverse (G : Mat4) (hG : IsUnit G.det)
    (v : Fin 4 → ℝ) (k : Fin 4) :
    (∑ p, G k p * ((1 / 2 : ℝ) * ∑ l, G⁻¹ p l * v l)) = (1 / 2 : ℝ) * v k := by
  change (G *ᵥ ((1 / 2 : ℝ) • (G⁻¹ *ᵥ v))) k = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hG,
    Matrix.one_mulVec]
  rfl

theorem lowered_christoffel (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) (i j k : Fin 4) :
    (∑ p, metricInChart g c z k p * christoffel g c z p i j) =
      (1 / 2 : ℝ) * (partialDeriv (fun w => metricInChart g c w j k) i z +
        partialDeriv (fun w => metricInChart g c w i k) j z -
        partialDeriv (fun w => metricInChart g c w i j) k z) := by
  exact matrix_lower_inverse (metricInChart g c z) hG _ k

theorem christoffel_metric_compatibility (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) (i j k : Fin 4) :
    (∑ p, (metricInChart g c z k p * christoffel g c z p i j +
      metricInChart g c z j p * christoffel g c z p i k)) =
      partialDeriv (fun w => metricInChart g c w j k) i z := by
  have hs (a b : Fin 4) : (fun w => metricInChart g c w a b) =
      (fun w => metricInChart g c w b a) := funext fun _ => g.symm _ _ _
  rw [Finset.sum_add_distrib, lowered_christoffel g c z hG,
    lowered_christoffel g c z hG, hs k j]
  ring

theorem christoffel_metric_compatibility_at_center (g : SmoothMetric M) (c : M)
    (i j k : Fin 4) :
    (∑ p, (chartMetric g c k p * christoffel g c (chartAt FourSpace c c) p i j +
      chartMetric g c j p * christoffel g c (chartAt FourSpace c c) p i k)) =
      partialDeriv (fun w => metricInChart g c w j k) i (chartAt FourSpace c c) := by
  apply christoffel_metric_compatibility
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (chartMetric_posDef g c).det_pos)

/-- Differentiating metric compatibility in two coordinate directions leaves
exactly the skew-adjointness equation for their curvature commutator. -/
theorem curvature_matrix_skew_of_metric_differentials (G A B C D : Mat4)
    (hmixed :
      Cᵀ * G + Bᵀ * (Aᵀ * G + G * A) + (Aᵀ * G + G * A) * B + G * C =
      Dᵀ * G + Aᵀ * (Bᵀ * G + G * B) + (Bᵀ * G + G * B) * A + G * D) :
    (C - D + A * B - B * A)ᵀ * G + G * (C - D + A * B - B * A) = 0 := by
  calc
    _ = (Cᵀ * G + Bᵀ * (Aᵀ * G + G * A) + (Aᵀ * G + G * A) * B + G * C) -
        (Dᵀ * G + Aᵀ * (Bᵀ * G + G * B) + (Bᵀ * G + G * B) * A + G * D) := by
      simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
      noncomm_ring
    _ = 0 := sub_eq_zero.mpr hmixed

end
end PositiveEinsteinFour.Geometry

end OAI
