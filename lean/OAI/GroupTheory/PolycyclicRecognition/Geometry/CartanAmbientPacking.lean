import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedSlicePacking

namespace OAI

/-! # Fixed-slice packing on the constructed ambient Cartan factors

The factor inclusions, normal action and published faithful realization now
supply every group-theoretic premise of the fixed-slice lower counting lemma.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold ENNReal

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- Actual ambient fixed-slice lower counting, with no assumed action
identification, embedding or Haar invariance. -/
theorem exists_ambient_fixedSlice_packing
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
      LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {r : ℝ} (hr : 0 < r) :
    ∃ (μ : Measure F.N.carrier) (C : ℝ≥0∞), μ.IsHaarMeasure ∧ C < ⊤ ∧
      (∀ (cost : M.wordList → ℝ) (β : M.Bases) (s R : ℝ), 0 ≤ R →
        μ (exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
          (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun i => cost (β.val i)) s) R) =
          ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
            ENNReal.ofReal (Real.exp (s * columnBasisWeight cost β.val)) *
              ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H)) ∧
      ∀ (x : G) (d : F.D.carrier) (K S : Set F.N.carrier), IsCompact K → S ⊆ K →
        ∃ t : Finset G, (↑t : Set G) ⊆ (fun u => x * F.inclusionN u * F.inclusionD d) '' S ∧
          (∀ y ∈ t, ∀ z ∈ t, y ≠ z → r < dist y z) ∧ μ S ≤ (t.card : ℝ≥0∞) * C := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  exact M.exists_uniform_fixedSlice_packing T hunimod F.N.equiv F.ExpN F.isExpN
    hbijN dynkinN haarN F.inclusionN F.inclusionD F.action
    (cartanLog H F.D.equiv F.ExpD hbijD) b₀
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExpG realize
      hbijN hbijD dynkinN d) F.conjugation F.closedN hr

end PolycyclicRecognition.CartanWordModel

end

end OAI
