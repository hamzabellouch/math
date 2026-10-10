import OAI.Geometry.RCD.Coordinates.NormalizationRebase

namespace OAI

/-! # Composing exact coordinate normalizations -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem transformedColumn_comp {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (A B : Euclidean n ≃L[ℝ] Euclidean n) :
    transformedColumn μ hQ (transformedColumn μ hQ u A) B =
      transformedColumn μ hQ u (B.trans A) := by
  funext i
  simp only [transformedColumn, sobolevColumnMap_transformed,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply]

theorem exact_mean_normalization_comp {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (A B : Euclidean n ≃L[ℝ] Euclidean n) (s : Set X) (hs : MeasurableSet s)
    (hB : IsExactMeanNormalization μ hQ
      (sobolevColumnMap μ hQ (transformedColumn μ hQ u A)) s hs B) :
    IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) s hs (B.trans A) := by
  change sobolevMeanGram μ hQ
    ((sobolevColumnMap μ hQ u).comp (B.trans A : Euclidean n →L[ℝ] Euclidean n)) s hs = _
  change sobolevMeanGram μ hQ
    ((sobolevColumnMap μ hQ (transformedColumn μ hQ u A)).comp
      (B : Euclidean n →L[ℝ] Euclidean n)) s hs = _ at hB
  rw [sobolevColumnMap_transformed] at hB
  exact hB

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
theorem normalization_values_comp {n : ℕ} (A B : Euclidean n ≃L[ℝ] Euclidean n)
    (v : X → Euclidean n) :
    (fun x => (B : Euclidean n →L[ℝ] Euclidean n).adjoint
      ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x))) =
      (fun x => (B.trans A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) := by
  have he : (B.trans A : Euclidean n →L[ℝ] Euclidean n) =
      (A : Euclidean n →L[ℝ] Euclidean n).comp (B : Euclidean n →L[ℝ] Euclidean n) := rfl
  rw [he, ContinuousLinearMap.adjoint_comp]
  rfl

omit [ProperSpace X] in
theorem firstOrderSplitting_comp {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (A B : Euclidean n ≃L[ℝ] Euclidean n) (v : X → Euclidean n) (p : X) (r ε : ℝ)
    (h : FirstOrderSplittingOn μ hQ p r ε
      (transformedColumn μ hQ (transformedColumn μ hQ u A) B)
      (fun x => (B : Euclidean n →L[ℝ] Euclidean n).adjoint
        ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)))) :
    FirstOrderSplittingOn μ hQ p r ε (transformedColumn μ hQ u (B.trans A))
      (fun x => (B.trans A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) := by
  rwa [transformedColumn_comp, normalization_values_comp] at h

end RegularPointCoordinates

end

end OAI
