import OAI.Geometry.EinsteinFour.WeylGeometry
import OAI.Geometry.EinsteinFour.ScalarNormalizer

namespace OAI

/-! Existence of the concrete orthonormal frames used for the curvature
blocks. This is obtained from the actual positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff MatrixOrder

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartMetric_apply (g : SmoothMetric M) (c : M) (i j : Fin 4) :
    chartMetric g c i j = g.inner c (coordinateVector i) (coordinateVector j) := by
  have hd : mfderiv I4 I4 (chartAt FourSpace c).symm (chartAt FourSpace c c) =
      ContinuousLinearMap.id ℝ FourSpace := by
    simpa [I4, extChartAt_coe_symm, extChartAt_coe, mfderivWithin_univ] using!
      (mfderivWithin_range_extChartAt_symm (I := I4) (x := c))
  simp only [chartMetric, metricInChart, hd]
  change g.inner ((chartAt FourSpace c).symm (chartAt FourSpace c c))
    (coordinateVector i) (coordinateVector j) = _
  rw [(chartAt FourSpace c).left_inv (mem_chart_source FourSpace c)]

theorem sum_coordinateVector (u : Fin 4 → ℝ) :
    (∑ i, u i • coordinateVector i) = WithLp.toLp 2 u := by
  ext j
  simp [coordinateVector, Pi.single_apply]

theorem chartMetric_pairing (g : SmoothMetric M) (c : M) (u v : Fin 4 → ℝ) :
    u ⬝ᵥ (chartMetric g c *ᵥ v) =
      g.inner c (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  rw [← sum_coordinateVector u, ← sum_coordinateVector v]
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner c
  change u ⬝ᵥ (chartMetric g c *ᵥ v) = B _ _
  have hB : B (∑ i, u i • coordinateVector i) (∑ j, v j • coordinateVector j) =
      ∑ i, ∑ j, u i * (v j * B (coordinateVector i) (coordinateVector j)) := by
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  rw [hB]
  simp only [dotProduct, mulVec, Finset.mul_sum, chartMetric_apply, B]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem chartMetric_posDef (g : SmoothMetric M) (c : M) :
    (chartMetric g c).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa [Matrix.conjTranspose_apply, chartMetric_apply] using
      g.symm c (coordinateVector j) (coordinateVector i)
  · intro u hu
    simp only [star_trivial]
    rw [chartMetric_pairing]
    apply g.pos
    intro hz
    apply hu
    exact (WithLp.toLp_injective 2) hz

/-- A fixed, canonical choice from the positive square root of the inverse
metric. No choice of curvature eigenvectors is needed for this frame. -/
def canonicalFrame (g : SmoothMetric M) (c : M) : OrthonormalFrame g c where
  matrix := Jacobi.scalarNormalizer (chartMetric g c)
  orthonormal := by
    have hsym := (Jacobi.scalarNormalizer_posSemidef (chartMetric g c)).isHermitian
    have ht : (Jacobi.scalarNormalizer (chartMetric g c))ᵀ =
        Jacobi.scalarNormalizer (chartMetric g c) := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hsym.eq
    rw [ht]
    exact Jacobi.scalarNormalizer_normalizes (chartMetric_posDef g c)

instance (g : SmoothMetric M) (c : M) : Nonempty (OrthonormalFrame g c) :=
  ⟨canonicalFrame g c⟩

end

end PositiveEinsteinFour.Geometry

end OAI
