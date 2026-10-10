import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborCompactProfiles
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

namespace OAI

/-! # Supported subsequential laws of the actual neighboring cell samples -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Compact containment gives a convergent subsequence of the original
translated Haar laws and a supported pair. The law is built from the actual
map `q ↦ (profile q, profile (q * step))`. -/
theorem exists_supported_neighbor_law
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (scale : ℕ → ℝ) (base step : ℕ → F.N.carrier)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S]
    (profile : ℕ → F.N.carrier → S) :
    ∃ (ν : ProbabilityMeasure (S × S)) (f : S × S) (u : ℕ → ℕ),
      StrictMono u ∧ f ∈ (ν : Measure (S × S)).support ∧
      Tendsto (fun n => ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
          E β (scale (u n)) (base (u n)))
        (fun q => (profile (u n) q, profile (u n) (q * step (u n))))) atTop (𝓝 ν) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let law := fun n => ProbabilityMeasure.map
    (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
      E β (scale n) (base n)) (fun q => (profile n q, profile n (q * step n)))
  obtain ⟨ν, u, hu, hν⟩ := CompactSpace.tendsto_subseq law
  have hne : (ν : Measure (S × S)) ≠ 0 := by
    intro he
    have hh := congrArg (fun μ : Measure (S × S) => μ univ) he
    simp at hh
  obtain ⟨f, hf⟩ := Measure.nonempty_support hne
  exact ⟨ν, f, u, hu, hf, hν⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
