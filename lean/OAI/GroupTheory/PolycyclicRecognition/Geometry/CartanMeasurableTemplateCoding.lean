import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoundedTemplatePaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MeasurableGeneratorPrefixes

namespace OAI

/-! # Measurable template words for independently sampled probe endpoints -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule Metric
open scoped Manifold

variable {EG G A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [MeasurableSpace A]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T in
/-- A Borel endpoint sampler in a bounded box admits a fixed letter pattern
with Borel bounded parameters. The length and amplitude constants work at
every scale and for every maximizing basis. -/
theorem exists_measurable_bounded_template_coding
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∀ y : A → closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) R,
        Measurable y →
      ∃ word : List (Fin M.letterCount × (A → ℝ)),
        word.length ≤ N ∧ (∀ z ∈ word, Measurable z.2) ∧
        (∀ x, ∀ z ∈ word, |z.2 x| ≤ C) ∧
        ∀ x, generatorGroupWord
          (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
          (F.ExpN ∘ F.N.equiv) (word.map (fun z => (z.1, z.2 x))) =
            F.ExpN (F.N.equiv (b.equivFun.symm (y x).val)) := by
  obtain ⟨N, C, hC, hcode⟩ := M.exists_continuous_bounded_template_coding T F
    hExp realize haarN dynkinN b₀ v R hR
  refine ⟨N, C, hC, ?_⟩
  intro r hr β hβ b y hy
  obtain ⟨word, hlen, hw, hamp, hend⟩ := hcode r hr β hβ
  let word' := word.map (fun z => (z.1, z.2 ∘ y))
  refine ⟨word', ?_, ?_, ?_, ?_⟩
  · simpa only [word', List.length_map] using hlen
  · intro z hz
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hz
    exact ((hw w hw').measurable).comp hy
  · intro x z hz
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hz
    exact hamp (y x) w hw'
  · intro x
    simpa only [word', List.map_map, Function.comp_def] using hend (y x)

end PolycyclicRecognition.CartanWordModel

end

end OAI
