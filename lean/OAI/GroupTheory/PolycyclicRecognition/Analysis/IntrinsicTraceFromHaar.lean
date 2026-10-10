import OAI.GroupTheory.PolycyclicRecognition.Analysis.TraceFromKernelHaar
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization

namespace OAI

/-! # Unimodularity forces zero adjoint trace without Dixmier -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G] [SimplyConnectedSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem trace_ad_eq_zero_of_intrinsic_kernel_haar
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : LinearMap.trace ℝ _ (ad ℝ _ x) = 0 := by
  let d := q.toLinearMap.comp (heightProjection T.character)
  have hd : Function.Surjective d := q.surjective.comp (heightProjection_surjective T.character)
  obtain ⟨s, hs, _, hsright⟩ :=
    exists_continuous_section_of_exponential_linear_quotient hExp d hd π hπExp
  let sC : C(Multiplicative W, G) := ⟨fun w => s w.toAdd, hs⟩
  have hsC (w : Multiplicative W) : π (sC w) = w := Multiplicative.ext (hsright w.toAdd)
  obtain ⟨N, ExpN, hExpN, ι, hι, _, hιExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ hπExp
  let b := finBasis ℝ T.kernelIdeal
  obtain ⟨c, hc, hhaar, hright⟩ := exists_height_kernel_coordinates T Exp hExp π N
    (nilpotentPublishedInputs.haar T.kernelIdeal N) ExpN hExpN ι hι hιExp hrange b
  have hdet := abs_det_conjugationDifferential_eq_one_of_height_coordinates
    T q Exp hExp π hπ hπExp sC hsC b c hc hhaar hright μ (Exp x)
  obtain ⟨m, _, j, ρ, _, _, _, _, hρ, he⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  rw [det_conjugationDifferential_exp T hExp j ρ hρ he,
    abs_of_pos (Real.exp_pos _)] at hdet
  exact (Real.exp_eq_one_iff _).mp hdet

end PolycyclicRecognition

end

end OAI
