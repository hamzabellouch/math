import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellTransport
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineSheetAgreement

namespace OAI

/-! # Marginals of the actual neighboring-sheet sampling law -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- A joint neighboring-sheet limit has precisely the two marginal limits
obtained by sampling the translated cells with suffixes `k₀` and `k₀ * k`.
Thus the single-sheet affinity theorem applies to both components. -/
theorem neighboring_cell_marginal_limits
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (scale : ℕ → ℝ) (k₀ k : ℕ → F.N.carrier)
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (k₀ n))
      (fun q => (profile n q, profile n (q * k n)))) atTop (𝓝 ν)) :
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (k₀ n))
      (profile n)) atTop (𝓝 (ProbabilityMeasure.map ν Prod.fst)) ∧
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β (scale n) (k₀ n * k n))
      (profile n)) atTop (𝓝 (ProbabilityMeasure.map ν Prod.snd)) := by
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
    E β (scale n) (k₀ n)
  let pair := fun n q => (profile n q, profile n (q * k n))
  have hp' n : Measurable (pair n) :=
    (hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)
  have hfst := sampled_projection_tendsto μ pair hp' ν hν Prod.fst continuous_fst
  have hsnd := sampled_projection_tendsto μ pair hp' ν hν Prod.snd continuous_snd
  refine ⟨hfst, ?_⟩
  convert hsnd using 1
  funext n
  exact (M.translated_groupBox_profile_law_mul_right T F hunimod eW haarN chartN hchartN
    b₀ E β (scale n) (k₀ n) (k n) (profile n) (hp n)).symm

end PolycyclicRecognition.CartanWordModel

end

end OAI
