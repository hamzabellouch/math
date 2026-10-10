import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledVisits
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSegmentSupportTimes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartPivot

namespace OAI

/-! # Actual support-switch paths for a segment through a word-chart pivot -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

/-- Every root switch uses the prescribed segment's own supporting endpoint.
Both the pivot polynomial bound and its exact height are consequences of the
word chart, rather than premises of this estimate. -/
theorem exists_segment_sampled_visit_bound
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
    (z : Fin (finrank ℝ H) → ℝ) (v : H) {T₀ ρ : ℝ} (hT₀ : 0 ≤ T₀) (hρ : 0 ≤ ρ) :
    let P := M.supportIn T hunimod eW
    let w₀ := eW (heightProjection T.character
      ((WordBasisSelections.basis X S βD).equivFun.symm z : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    let u := eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    let E := segment ℝ w₀ (w₀ + T₀ • u)
    let θ := P.segmentSupportTime u T₀
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ n : G, ∀ i b,
      |b| ≤ 2 * ρ →
      PathMetricBound (M.sampledDirectionalVisitPath T hExp realize (θ i • v) i n
        (wordChartPivot X S βD r z) r (P.weightSupport E i) b)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        dist (n * Exp (((t * b) * Real.exp (r * P.weightSupport E i)) •
              (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp ((wordChartPivot X S βD r z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) * Exp (r • (θ i • v : H))))
          (n * Exp (((t' * b) * Real.exp (r * P.weightSupport E i)) •
              (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) *
            (Exp ((wordChartPivot X S βD r z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G) * Exp (r • (θ i • v : H)))) ≤
          C * Real.log (2 + r) := by
  dsimp only
  let P := M.supportIn T hunimod eW
  let h : H →ₗ[ℝ] W := eW.toLinearMap.comp
    ((heightProjection T.character).comp H.incl.toLinearMap)
  let w₀ := h ((WordBasisSelections.basis X S βD).equivFun.symm z)
  let u := h v
  let θ := P.segmentSupportTime u T₀
  let E := segment ℝ w₀ (w₀ + T₀ • u)
  obtain ⟨A, p, hA, hbound⟩ := wordChartPivot_polynomial_bound X S βD (finBasis ℝ H) z
  have hh (x y : H) : h ⁅x, y⁆ = 0 := by
    change eW (heightProjection T.character ⁅(x : GroupLieAlgebra (𝓘(ℝ, EG)) G), y⁆) = 0
    rw [T.height_lie, map_zero]
  have hs (i : Fin M.letterCount) : cartanHeightWeight T H (M.weight i)
      (eW.symm (w₀ + eW (heightProjection T.character ((θ i • v : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) =
      P.weightSupport E i :=
    M.segment_visit_direction_support T hunimod eW v w₀ hT₀ i
  obtain ⟨C, hC, hv⟩ := M.exists_sampled_directional_visit_bound T F hExp realize haarD dynkinD
    eW π hπ (fun i => θ i • v) w₀ (P.weightSupport E) hs hA hρ p
  refine ⟨C, hC, ?_⟩
  intro r hr n i b hb
  have hheight : (π (Exp ((wordChartPivot X S βD r z : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))).toAdd = r • w₀ := by
    rw [hπ]
    exact wordChartPivot_height X S βD h hh hr z
  exact hv r (zero_le_one.trans hr) _ (hbound r hr) hheight n i b hb

end PolycyclicRecognition.CartanWordModel

end

end OAI
