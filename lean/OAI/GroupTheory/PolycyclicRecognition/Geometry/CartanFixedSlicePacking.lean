import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHaarConjugation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FixedSlicePacking

namespace OAI

/-! # Lower packing for actual Cartan slices

The nilpotent parameter measure has its computed word-box volume. Its
invariance under the full Cartan action makes one finite packing constant
work at every Cartan position and every translated basepoint.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)
  (haar : NilpotentExponentialHaarInput EN N)
  {D G : Type*} [Group D] [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N) (logD : D → H)

include hunimod haar in
/-- The fixed-slice packing constant is finite and independent of basepoint,
Cartan position and compact endpoint set. The same Haar measure has the exact
weighted-box formula from the Lie model. -/
theorem exists_uniform_fixedSlice_packing
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, φ d = M.adjointGroupAutomorphism T eN Exp hExp hbij dynkin (logD d))
    (hconj : ∀ d u, ι (φ d u) = κ d * ι u * (κ d)⁻¹)
    (hι : Topology.IsClosedEmbedding ι) {r : ℝ} (hr : 0 < r) :
    ∃ (μ : Measure N) (C : ℝ≥0∞), μ.IsHaarMeasure ∧ C < ⊤ ∧
      (∀ (cost : M.wordList → ℝ) (β : M.Bases) (s R : ℝ), 0 ≤ R →
        μ (exponentialCoordinateBox (Exp ∘ eN)
          (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun i => cost (β.val i)) s) R) =
          ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
            ENNReal.ofReal (Real.exp (s * columnBasisWeight cost β.val)) *
              ENNReal.ofReal (2 * R) ^ finrank ℝ (cartanRootIdeal H)) ∧
      ∀ (x : G) (d : D) (K S : Set N), IsCompact K → S ⊆ K →
        ∃ t : Finset G, (↑t : Set G) ⊆ (fun u => x * ι u * κ d) '' S ∧
          (∀ y ∈ t, ∀ z ∈ t, y ≠ z → r < dist y z) ∧ μ S ≤ (t.card : ℝ≥0∞) * C := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  obtain ⟨μ, hμ, hinv, hvol⟩ := M.exists_haar_adjoint_invariant_weighted_boxes T hunimod
    eN Exp hExp hbij dynkin haar b₀
  let : μ.IsHaarMeasure := hμ
  have hpres (d : D) : MeasurePreserving (φ d) μ μ := by
    rw [hφ]
    exact hinv (logD d)
  refine ⟨μ, μ (ι ⁻¹' closedBall (1 : G) r), hμ, ?_, hvol, ?_⟩
  · exact fixedSlice_packing_constant_lt_top ι μ hι r
  · intro x d K S hK hS
    exact exists_fixedSlice_separated_net_of_compact ι κ φ μ hpres hconj
      hι.continuous x d hK hS hr

end PolycyclicRecognition.CartanWordModel

end

end OAI
