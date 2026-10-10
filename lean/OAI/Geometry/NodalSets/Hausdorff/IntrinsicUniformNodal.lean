import OAI.Geometry.NodalSets.Elliptic.IntrinsicWeightedLift
import OAI.Geometry.NodalSets.Hausdorff.OriginalCoefficientNodalTransfer

namespace OAI

namespace Yau.Target
open Manifold Set MeasureTheory Yau.Jets
open scoped ContDiff NNReal ENNReal RealInnerProductSpace
noncomputable section

lemma uniform_intrinsic_coefficient_nodal_transfer
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r) (hR0 : 0 < R)
    (p : Manifold5) (s : ℝ) {t : ℝ} (ht : t ≠ 0) {K : Set (Coord × ℝ)}
    (hK : IsCompact K) (hKD : K ⊆ productChartDomain p s t) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
        (hs : ∀ x v w, A x v w = A x w v)
        (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
        (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x),
        (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
          a*‖v‖^2 ≤ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v)) →
        (∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
          A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ b*‖v‖^2) →
        (∀ x, r ≤ rho x) → (∀ x, rho x ≤ R) →
        ∀ (u : Manifold5 → ℝ) (Z : Set (Coord × ℝ)), Z ⊆ K →
          (∀ z ∈ Z, u (productChartInverse p s t z) = 0) →
          Measure.hausdorffMeasure (4:ℝ) Z ≤ (C:ℝ≥0∞)^4 *
            nodalMeasure (intrinsicWeightedMetric A hA hs hp rho hr hrp) u := by
  obtain ⟨C,hC,hbound⟩ := uniform_original_coefficient_nodal_transfer
    (min a 1) (max b 1) r R (lt_min ha zero_lt_one) (lt_max_of_lt_left hb) hr0 hR0
    p s ht hK hKD
  refine ⟨C,hC,?_⟩
  intro A hA hs hp rho hr hrp hlo hhi hrho hR
  exact hbound (intrinsicAmbientMatrix A) rho (intrinsicAmbientMatrix_smooth A hA)
    (intrinsicAmbientMatrix_posDef A hs hp) hr hrp
    (fun x v ↦ (intrinsicAmbientMatrix_bounds A a b hlo hhi x v).1)
    (fun x v ↦ (intrinsicAmbientMatrix_bounds A a b hlo hhi x v).2) hrho hR

end
end Yau.Target

end OAI
