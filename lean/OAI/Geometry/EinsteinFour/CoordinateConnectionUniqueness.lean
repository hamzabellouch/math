import OAI.Geometry.EinsteinFour.CoordinateMetricCompatibility

namespace OAI

/-! The coordinate Levi-Civita coefficients are determined by torsion
freeness and metric compatibility. This is the uniqueness step used when
changing charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem christoffel_eq_of_compatible (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det)
    (C : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym : ∀ p i j, C p i j = C p j i)
    (hcompat : ∀ i j k,
      (∑ p, (metricInChart g c z k p * C p i j +
        metricInChart g c z j p * C p i k)) =
        partialDeriv (fun w => metricInChart g c w j k) i z) :
    C = christoffel g c z := by
  funext p i j
  have hv : metricInChart g c z *ᵥ (fun q => C q i j) =
      metricInChart g c z *ᵥ (fun q => christoffel g c z q i j) := by
    funext k
    change (∑ q, metricInChart g c z k q * C q i j) = _
    rw [show (metricInChart g c z *ᵥ (fun q => christoffel g c z q i j)) k =
      ∑ q, metricInChart g c z k q * christoffel g c z q i j from rfl,
      lowered_christoffel g c z hG]
    have h1 := hcompat i j k
    have h2 := hcompat j i k
    have h3 := hcompat k i j
    simp only [Finset.sum_add_distrib] at h1 h2 h3
    simp_rw [hsym _ j i] at h2
    simp_rw [hsym _ k i, hsym _ k j] at h3
    linarith only [h1, h2, h3]
  have h := congrArg (fun v => (metricInChart g c z)⁻¹ *ᵥ v) hv
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG,
    Matrix.one_mulVec] at h
  exact congrFun h p

end
end PositiveEinsteinFour.Geometry

end OAI
