import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure

namespace OAI

/-! # Exponential Haar coordinates on the actual canonical-height kernel -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W)

include hExp in
omit [NormedSpace ℝ W] in
theorem exists_height_kernel_coordinates
    (N : NilpotentLieModel T.kernelIdeal)
    (haarN : NilpotentExponentialHaarInput N.modelSpace N.carrier)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN)
    (ι : N.carrier →* G) (hι : Topology.IsClosedEmbedding ι)
    (hιExp : ∀ x : T.kernelIdeal, ι (ExpN (N.equiv x)) = Exp x)
    (hrange : Set.range ι = (π.ker : Set G))
    (b : Basis (Fin (finrank ℝ T.kernelIdeal)) ℝ T.kernelIdeal) :
    ∃ c : (Fin (finrank ℝ T.kernelIdeal) → ℝ) ≃ₜ π.ker,
      (∀ v, (c v : G) = Exp (b.equivFun.symm v)) ∧
      (Measure.map c volume).IsHaarMeasure ∧
      (Measure.map c volume).IsMulRightInvariant := by
  let : IsTopologicalGroup N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, N.modelSpace)) ⊤
  obtain ⟨cN, hcN⟩ := (haarN.2 ExpN hExpN (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  let κ := kernelRealization π ι hι hrange
  let γ : (Fin (finrank ℝ T.kernelIdeal) → ℝ) ≃ₜ N.carrier :=
    (b.equivFun.symm.trans N.equiv.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans cN
  let c := γ.trans κ.toHomeomorph
  have hγ : (γ : (Fin (finrank ℝ T.kernelIdeal) → ℝ) → N.carrier) =
      (ExpN ∘ N.equiv) ∘ b.equivFun.symm := by
    funext v
    exact hcN _
  let ν := Measure.map ((ExpN ∘ N.equiv) ∘ b.equivFun.symm) volume
  let : ν.IsHaarMeasure :=
    exponential_basis_measure_isHaar haarN N.equiv T.kernelIdeal_nilpotent ExpN hExpN b
  have hcmap : Measure.map c volume = Measure.map κ ν := by
    change Measure.map (κ.toHomeomorph ∘ γ) volume = Measure.map κ.toHomeomorph ν
    rw [← Measure.map_map κ.continuous.measurable γ.continuous.measurable]
    congr 1
    change Measure.map γ volume = ν
    rw [hγ]
  have hhaar : (Measure.map c volume).IsHaarMeasure := by
    rw [hcmap]
    exact κ.isHaarMeasure_map ν
  have hc (v) : (c v : G) = Exp (b.equivFun.symm v) := by
    change ι (γ v) = _
    rw [hγ]
    exact hιExp _
  refine ⟨c, hc, hhaar, ?_⟩
  let : (Measure.map c volume).IsHaarMeasure := hhaar
  apply isMulRightInvariant_map_of_neg volume c c.continuous.measurable
  intro v
  apply Subtype.ext
  change (c (-v) : G) = (c v : G)⁻¹
  rw [hc, hc, map_neg]
  exact hExp.map_neg _

end PolycyclicRecognition

end

end OAI
