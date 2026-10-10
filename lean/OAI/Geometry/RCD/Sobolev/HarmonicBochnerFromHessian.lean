import OAI.Geometry.RCD.Sobolev.PoissonHessianInput
import OAI.Geometry.RCD.Sobolev.PoissonSpanLift

namespace OAI

/-! # Harmonic Bochner calculus from the Poisson Hessian input

The n-dimensional harmonic span embeds isometrically into the existing
(n+2)-dimensional Poisson span. Restricting the full positive measure to
that subspace proves the harmonic Bochner input, including its original
extension bound, without a separate assumption.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section
namespace RegularPointCoordinates

def harmonicCoordinateInclusion (n : ℕ) : Euclidean n →ₗᵢ[ℝ] Euclidean (n + 2) where
  toFun := poissonCoordinateLift
  map_add' u v := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [poissonCoordinateLift, Fin.append_left, Fin.append_right]
  map_smul' c v := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [poissonCoordinateLift, Fin.append_left, Fin.append_right]
  norm_map' := poissonCoordinateLift_norm

private def harmonicMeasureRestriction {X : Type*} [MeasurableSpace X] {n : ℕ}
    (M : PositiveBilinearMeasure X (Euclidean (n + 2))) :
    PositiveBilinearMeasure X (Euclidean n) where
  bilinear := M.bilinear.compl₁₂ (harmonicCoordinateInclusion n).toLinearMap
    (harmonicCoordinateInclusion n).toLinearMap
  symmetric v w := M.symmetric (harmonicCoordinateInclusion n v) (harmonicCoordinateInclusion n w)
  nonneg v := M.nonneg (harmonicCoordinateInclusion n v)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
/-- The separate harmonic Bochner premise is a consequence of the already
required Poisson Hessian specialization of Gigli--Han. -/
theorem LocalPoissonHessianInput.harmonicBochnerInput {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (h : LocalPoissonHessianInput hX) :
    LocalHarmonicBochnerInput hX := by
  intro κ hκ hK p r hr L U hU hgrad
  let I := harmonicCoordinateInclusion n
  let P := I.toContinuousLinearMap.adjoint
  have hPI (v : Euclidean n) : P (I v) = v := by
    apply ext_inner_right ℝ
    intro w
    change inner ℝ (I.toContinuousLinearMap.adjoint (I v)) w = inner ℝ v w
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact I.inner_map_map v w
  have hPnorm : ‖P‖ ≤ 1 := by
    change ‖ContinuousLinearMap.adjoint I.toContinuousLinearMap‖ ≤ 1
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact I.norm_toContinuousLinearMap_le
  let V := U.comp P
  have hV (v : Euclidean (n + 2)) :
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8 * r)) (V v)
        ((0 : Euclidean (n + 2) →ₗ[ℝ] ℝ) v) :=
    (isConstantLaplacianOn_zero_iff _ _ _ _).mpr (hU (P v))
  have hVgrad (v : Euclidean (n + 2)) :
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
        localGamma (hausdorff n X) hX.quadratic (V v) (V v) x ≤
          (L : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    have hp : ‖P v‖ ≤ ‖v‖ :=
      (P.le_opNorm v).trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hPnorm (norm_nonneg v))
    filter_upwards [hgrad (P v)] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp 2)
      (sq_nonneg _))
  obtain ⟨M, hM, _, _⟩ := h κ hκ hK p r hr L V 0 hV hVgrad
  refine ⟨harmonicMeasureRestriction M, ?_⟩
  intro v
  obtain ⟨G⟩ := hM (I v)
  have hVI : V (I v) = U v := by simp only [V, ContinuousLinearMap.comp_apply, hPI]
  refine ⟨{ energy := G.energy, representative := ?_, bounded := ?_, measure_laplacian := ?_ }⟩
  · simpa only [hVI] using G.representative
  · simpa only [I.nnnorm_map] using G.bounded
  · have hs : harmonicBochnerSource (hausdorff n X) hX.quadratic U
        (harmonicMeasureRestriction M) κ v =
        harmonicBochnerSource (hausdorff n X) hX.quadratic V M κ (I v) := by
      simp only [harmonicBochnerSource, hVI]
      rfl
    rw [hs]
    exact G.measure_laplacian

end RegularPointCoordinates

end

end OAI
