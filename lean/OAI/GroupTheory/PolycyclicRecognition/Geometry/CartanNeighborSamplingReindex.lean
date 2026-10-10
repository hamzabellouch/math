import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSamplingRow

namespace OAI

/-! # Cofinal restriction of the original neighboring samples -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [Fintype I] [DecidableEq I]
  (π : G →* Multiplicative W)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (β : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (B δ : ℝ)
  (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
  {Λ : ℝ≥0}
  (D : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
    haarN chartN hchartN pivot B δ Profiles (Λ := Λ))

/-- Every increasing subsequence keeps the original limiting law. -/
def NeighborSamplingRow.reindex (u : ℕ → ℕ) (hu : StrictMono u) :
    NeighborSamplingRow T M F hunimod eW π bN cell β X βD
      haarN chartN hchartN pivot B δ Profiles (Λ := Λ) where
  scale := D.scale ∘ u
  grows := D.grows.comp hu.tendsto_atTop
  strict_mono := D.strict_mono.comp hu
  scale_ge_one := fun n => D.scale_ge_one (u n)
  pair := D.pair ∘ u
  center := D.center ∘ u
  radius := D.radius ∘ u
  radius_nonneg := fun n => D.radius_nonneg (u n)
  radius_subexponential := fun ε hε => hu.tendsto_atTop.eventually (D.radius_subexponential ε hε)
  base := D.base ∘ u
  step := D.step ∘ u
  base_mem := fun n => D.base_mem (u n)
  step_mem := fun n => D.step_mem (u n)
  mode := D.mode
  time := D.time ∘ u
  time_bound := fun n => D.time_bound (u n)
  root_step := fun n => D.root_step (u n)
  profile := D.profile ∘ u
  measurable_profile := fun n => D.measurable_profile (u n)
  actual := fun n => D.actual (u n)
  law := D.law
  converges := D.converges.comp hu.tendsto_atTop
  point := D.point
  supported := D.supported

end PolycyclicRecognition.CartanWordModel

end

end OAI
