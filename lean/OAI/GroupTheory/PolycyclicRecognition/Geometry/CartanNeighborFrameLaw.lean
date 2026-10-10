import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellTransport
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellProbability
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProbabilityTransport
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledProbeFrames

namespace OAI

/-! # The same neighboring law in the actual cube-sampled frames -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set
open scoped Manifold ENNReal

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

/-- Sampling the two fixed endpoints with one cube variable is exactly the
original neighboring Haar-cell law, with its original base and step. -/
theorem cube_neighbor_frame_law
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (r : ℝ)
    (base finish step : F.N.carrier) (hfinish : finish = base * step)
    {X : Type*} [MeasurableSpace X]
    (profile : F.N.carrier → X) (hp : Measurable profile) :
    ProbabilityMeasure.map
      (cellProbabilityMeasure volume
        (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)))
        (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (fun y =>
        (profile (F.sampleRoot (M.boxBasis T hunimod eW E β r) y * base),
         profile (F.sampleRoot (M.boxBasis T hunimod eW E β r) y * finish))) =
      ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀ E β r base)
        (fun q => (profile q, profile (q * step))) := by
  have he := M.cube_profile_law_eq_cell_profile_law T F hunimod eW
    haarN chartN hchartN b₀ E β r base
    (fun q => (profile q, profile (q * step)))
    (hp.prodMk (hp.comp (continuous_id.mul continuous_const).measurable))
  simpa only [Function.comp_def, CartanFactorModel.sampleRoot, hfinish, mul_assoc] using he

end PolycyclicRecognition.CartanWordModel

end

end OAI
