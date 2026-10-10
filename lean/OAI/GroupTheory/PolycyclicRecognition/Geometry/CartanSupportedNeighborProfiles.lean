import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborLawCompactness
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAllowedProfileCompactness
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSuffixRate
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellProbability
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurableProbeProfiles

namespace OAI

/-! # Compact measurable profiles on the original two neighboring cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

/-- The original neighboring cells admit measurable profiles in one compact
family and a supported joint subsequential limit. Only the cited Lie inputs
and the original box bounds are assumptions. -/
theorem exists_supported_measurable_neighbor_profiles
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' E) β (scale n) (R n))
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n)) (x : ℕ → G) :
    ∃ (S : Set C((Fin (finrank ℝ H) → ℝ), W)), IsCompact S ∧
      ∃ (index : ℕ → ℕ) (profile : ℕ → F.N.carrier → S)
        (ν : ProbabilityMeasure (S × S)) (f : S × S),
        StrictMono index ∧ (∀ n, Measurable (profile n)) ∧
        f ∈ (ν : Measure (S × S)).support ∧
        Tendsto (fun n => ProbabilityMeasure.map
          (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
            E β (scale (index n)) (base (index n)))
          (fun q => (profile n q, profile n (q * step (index n))))) atTop (𝓝 ν) ∧
        ∀ n q, q ∈ (fun v => v * base (index n)) ''
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (index n)) 1 ∪
          (fun v => v * base (index n) * step (index n)) ''
            M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale (index n)) 1 → ∀ z,
          (profile n q).val z = rescaledMapProfile (J (index n)) (x (index n)) (F.inclusionN q)
            (max (Real.log (scale (index n))) 0)
            (fun z => F.inclusionD (F.ExpD (F.D.equiv
              ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
                (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
                (max (Real.log (scale (index n))) 0)).equivFun.symm z)))) z := by
  obtain ⟨n₀, S, hS, profile, hp, hactual⟩ :=
    M.exists_compact_measurable_neighbor_profiles T F hunimod eW hExp realize
      haarN haarD dynkinN dynkinD chartN hchartN X hDnil hletters bD₀ βD hβD
      b₀ hE hne β hβ hweights hδ scale R hscale hscale1 hR0 hR base step hbase hstep J hJ x
  obtain ⟨ν, f, u, hu, hf, hν⟩ := M.exists_supported_neighbor_law T F hunimod eW
    haarN chartN hchartN b₀ E β (fun n => scale (n + n₀))
    (fun n => base (n + n₀)) (fun n => step (n + n₀)) S hS profile
  refine ⟨S, hS, fun n => u n + n₀, fun n => profile (u n), ν, f,
    hu.add_const n₀, fun n => hp (u n), hf, hν, ?_⟩
  intro n q hq z
  exact hactual (u n) q hq z

end PolycyclicRecognition.CartanWordModel

end

end OAI
