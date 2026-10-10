import OAI.Geometry.EinsteinFour.ChartMetricSmoothness

namespace OAI

/-! The pulled-back metric is positive definite everywhere in its chart,
not merely at the chart's center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff MatrixOrder

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_inverse_derivative_injective (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    Function.Injective (mfderiv I4 I4 (chartAt FourSpace c).symm z) := by
  exact (mdifferentiable_chart (I := I4) c).symm.mfderiv_injective hz

theorem metricInChart_pairing (g : SmoothMetric M) (c : M) (z : FourSpace)
    (u v : Fin 4 → ℝ) :
    u ⬝ᵥ (metricInChart g c z *ᵥ v) =
      g.inner ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (WithLp.toLp 2 u))
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (WithLp.toLp 2 v)) := by
  rw [← sum_coordinateVector u, ← sum_coordinateVector v]
  let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner ((chartAt FourSpace c).symm z)
  change u ⬝ᵥ (metricInChart g c z *ᵥ v) = B (D _) (D _)
  have hB : B (D (∑ i, u i • coordinateVector i))
      (D (∑ j, v j • coordinateVector j)) =
      ∑ i, ∑ j, u i * (v j * B (D (coordinateVector i)) (D (coordinateVector j))) := by
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  rw [hB]
  simp only [dotProduct, mulVec, Finset.mul_sum, metricInChart, B, D]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem metricInChart_posDef (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) : (metricInChart g c z).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    change metricInChart g c z j i = metricInChart g c z i j
    exact g.symm ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (coordinateVector j))
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (coordinateVector i))
  · intro u hu
    simp only [star_trivial]
    rw [metricInChart_pairing]
    apply g.pos
    intro hzero
    apply hu
    apply WithLp.toLp_injective 2
    change WithLp.toLp 2 u = (0 : FourSpace)
    apply chart_inverse_derivative_injective c z hz
    let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
    change D (WithLp.toLp 2 u) = D 0
    rw [map_zero]
    exact hzero

end
end PositiveEinsteinFour.Geometry

end OAI
