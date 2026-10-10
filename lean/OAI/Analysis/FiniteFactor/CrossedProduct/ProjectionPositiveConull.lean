import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionDiagonal
import OAI.Analysis.FiniteFactor.CrossedProduct.InvariantConull

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- The strict diagonal conclusion and every previously verified orbit identity
hold on one invariant Borel conull set for the original candidate projection. -/
theorem sourceProjection_positive_common_conull
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∃ Q : Set SourceTorus, MeasurableSet Q ∧ (∀ᵐ z ∂sourceTorusHaar, z ∈ Q) ∧
      (∀ z ∈ Q,
        finiteFloorSupport θ (sourceTorusRepresentative z) ∧
        IsStarProjection (sourceTorusOperatorField p z) ∧
        (∀ r k m : ℤ, (sourceTorusOperatorField p (sourceTorusRotate θ r z)
          (lp.single 2 m (1 : ℂ))) k =
          (sourceTorusOperatorField p z (lp.single 2 (m+r) (1 : ℂ))) (k+r)) ∧
        (∀ n : ℕ, (∀ i, sourceTorusRepresentative z i ≤
          sourceTorusRepresentative (sourceTorusRotate θ n z) i) →
          (z,sourceTorusRotate θ n z) ∈ sourceCappedPairZeroSet θ p) ∧
        0 < (sourceCentralCoefficient p (sourceTorusRepresentative z)).re ∧
        (sourceCentralCoefficient p (sourceTorusRepresentative z)).re < 1 ∧
        (sourceCentralCoefficient p (sourceTorusRepresentative z)).im = 0) ∧
      (∀ n : ℤ, ∀ z ∈ Q, sourceTorusRotate θ n z ∈ Q) := by
  obtain ⟨Q,hQ,hQa,hQp,_⟩ := sourceProjection_common_conull θ hθ hp hproj hinv
  have hd := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceProjection_strict_diagonal θ hθ hr hp hproj hp0 hp1 hinv)
  obtain ⟨R,hR,hRa,hRp,hRi⟩ := exists_source_invariant_conull θ
    (fun z => z ∈ Q ∧ 0 < (sourceCentralCoefficient p (sourceTorusRepresentative z)).re ∧
      (sourceCentralCoefficient p (sourceTorusRepresentative z)).re < 1 ∧
      (sourceCentralCoefficient p (sourceTorusRepresentative z)).im = 0) (hQa.and hd)
  refine ⟨R,hR,hRa,?_,hRi⟩
  intro z hz
  have hh := hQp z (hRp z hz).1
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,(hRp z hz).2⟩

end
end FiniteFactor

end OAI
