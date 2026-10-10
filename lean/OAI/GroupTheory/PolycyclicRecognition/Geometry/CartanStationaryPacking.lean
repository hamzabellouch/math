import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanStationaryPaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoordinatePacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateStationaryPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedEndpointMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-! # Stationary good paths to actual rescaled endpoints

Independent normalized coordinate volume and continuous endpoint coding
instantiate the stationary sampling theorem. A single normalized pair is
therefore good on an exponentially large ambient separated endpoint set.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T in
/-- Actual separated endpoints with controlled image paths and the exact exponential lower rate. -/
theorem exists_stationary_segment_separated_set
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (v : H)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (ε C : ℝ) (Q : ℝ≥0∞) (β : M.Bases), 0 < ε ∧ 0 ≤ C ∧ Q < ⊤ ∧
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val ∧
      ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      ∀ r : ℝ, r₀ ≤ r → ∃ (p : NormalizedPair G Λ) (t : Finset G),
        (∀ x ∈ t, ∀ y ∈ t, x ≠ y → ρ < dist x y) ∧
        ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight
            (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val)) *
          volume (ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε) * (1 / 2) ≤
            (t.card : ℝ≥0∞) * Q ∧
        ∀ g ∈ t, ∃ γ : Path (1 : G) g,
          PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
          ∀ u, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd,
            ‖pairHeight π (γ u) p - r • z‖ ≤
              (K * Λ * C * δ + η) * r + K * Λ * C * (1 + Real.log (2 + r)) := by
  classical
  obtain ⟨ε, C, β, hε, hC, hβ, hpaths⟩ := M.exists_stationary_good_segment_paths T F
    hExp realize haarN dynkinN μ π l hπ hl hK hL hLip hbound hsub b₀ v
  obtain ⟨Q, hQ, hpack⟩ := M.exists_coordinate_subset_packing T F haarN b₀ hρ
  refine ⟨ε, C, Q, β, hε, hC, hQ, hβ, ?_⟩
  intro δ hδ η hη
  obtain ⟨r₀, hr₀, hgood⟩ := hpaths δ hδ η hη
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  obtain ⟨p, B, hB, hvolume, hcontrol⟩ := hgood r hr
  let S := Subtype.val '' Bᶜ
  have hS : S ⊆ closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε := by
    rintro y ⟨z, _, rfl⟩
    exact ball_subset_closedBall z.property
  obtain ⟨t, ht, hsep, hcount⟩ := hpack
    (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β r ε S hS
  refine ⟨p, t, hsep, ?_, ?_⟩
  · calc
      _ = (ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates M.letter M.wordList b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight
            (fun w : M.wordList => bracketWordExponent (M.segmentSupportExponent v) w) β.val))) *
          (volume (ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε) * (1 / 2)) := by ac_rfl
      _ ≤ _ := mul_le_mul' le_rfl hvolume
      _ ≤ _ := hcount
  · intro g hg
    obtain ⟨y, hy, he⟩ := ht hg
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨γ, hγ, hh⟩ := hcontrol z hz
    exact ⟨γ.cast rfl he.symm, hγ.cast rfl he.symm, hh⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
