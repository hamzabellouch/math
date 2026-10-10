import Mathlib
import OAI.Analysis.Crouzeix.SimilarityRepresentation

namespace OAI

/-! Physical Comparison. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

theorem endpoint_le_two_of_physical_tests {n : ℕ}
    (M : BoundaryL2 n →L[ℝ] BoundaryL2 n) (hM : ‖M‖ ≤ 1)
    (E Λ F : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (hΛ : ∀ t, (Λ t).PosSemidef)
    (hmass : ∫ t, Λ t ∂circleMeasure = 1) (hF : ∀ t, ‖F t‖ ≤ 1)
    (hleft : (boundaryCauchy M).comp
        ((lpLeft F F.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M)) =
      (lpLeft F F.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M))
    (hright : (boundaryCauchy M).comp
        ((lpRight F F.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M)) =
      (lpRight F F.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M))
    (S : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)) (hS : IsSelfAdjoint S)
    (X Y : Coeff n) (hX : ‖vectorization X‖ = 1) (hY : ‖vectorization Y‖ = 1)
    (hXY : Xᴴ * Y = 0) (κ : ℝ) (hκ : 0 < κ)
    (hx : S (vectorization X) = (κ : ℂ) • vectorization X)
    (hy : S (vectorization Y) = vectorization Y)
    (hI : tensorIntegral Λ F (vectorization X) = vectorization Y)
    (htest : ∀ (j : ℤ × (Fin n × Fin n)) (c : ℂ),
      ∃ (V W : C(CircleSpace, Coeff n))
        (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
        boundaryCauchy M (boundaryField (matrixLaurentMonomial j c)) = boundaryField V ∧
        boundaryCauchy M (lpStar (boundaryField (matrixLaurentMonomial j c))) =
          boundaryField W ∧
        tensorIntegral E (matrixLaurentMonomial j c) = B + L.adjoint ∧
        S * B = tensorIntegral Λ V * S ∧ S * L = tensorIntegral Λ W * S) :
    κ ≤ 2 := by
  have hy' : S (vectorization Y) = ((1 : ℝ) : ℂ) • vectorization Y := by
    simpa only [Complex.ofReal_one, one_smul] using hy
  have hP := projected_density_of_laurent_testing M E Λ
    (fun t => (hE t).isHermitian) (fun t => (hΛ t).isHermitian) S hS
    X X κ κ hκ.ne' hκ.ne' hx hx htest
  simp only [div_self hκ.ne', one_smul] at hP
  have hQ := projected_density_of_laurent_testing M E Λ
    (fun t => (hE t).isHermitian) (fun t => (hΛ t).isHermitian) S hS
    Y Y 1 1 one_ne_zero one_ne_zero hy' hy' htest
  simp only [div_one, one_smul] at hQ
  have hR := projected_density_of_laurent_testing M E Λ
    (fun t => (hE t).isHermitian) (fun t => (hΛ t).isHermitian) S hS
    X Y κ 1 hκ.ne' one_ne_zero hx hy' htest
  simp only [div_one, one_div] at hR
  have hord := densityLp_ordered Λ F hΛ hmass hF X Y (hX.trans hY.symm) hI
  refine fourier_ordered_comparison M hM F F.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hF) ?_ ?_
    (densityLp Λ X X) (densityLp Λ Y Y) (densityLp Λ X Y)
    (densityLp_self_hermitian Λ hΛ X) (densityLp_self_hermitian Λ hΛ Y)
    (hord.mono fun _ ht => ht.1) (hord.mono fun _ ht => ht.2.2)
    (matrixMean_cross_zero Λ hmass X Y hXY) ?_ κ hκ ?_
  · simpa only [adjoint_boundaryCauchyAdjoint] using hleft
  · simpa only [adjoint_boundaryCauchyAdjoint] using hright
  · rw [trace_matrixMean_self_one Λ hmass X hX, Complex.one_re]
    exact zero_lt_one
  · have hb := densityLp_block_posSemidef E hE X Y
    rw [hP, hQ, hR] at hb
    exact hb

end CrouzeixHilbert.Boundary

end

end OAI
