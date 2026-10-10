import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledImageVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRightHaar

namespace OAI

/-! # Haar properties of the exact measure used by the image-volume formula -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The published input gives Haar invariance to this specific coordinate
measure, so recurrence and the determinant formula use the same normalization. -/
theorem exponential_basis_measure_isHaar
    (haar : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {n : ℕ} (b : Basis (Fin n) ℝ L) :
    (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume).IsHaarMeasure := by
  have he : ((Exp ∘ e) ∘ b.equivFun.symm) =
      Exp ∘ (b.map e.toLinearEquiv).equivFun.symm := by
    funext x
    rw [Basis.map_equivFun]
    rfl
  rw [he]
  exact (haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)).2 n _

/-- Inversion corresponds to coordinate negation. Thus the same measure
is also right invariant, as required by backward recurrence. -/
theorem exponential_basis_measure_isRightInvariant
    (haar : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {n : ℕ} (b : Basis (Fin n) ℝ L) :
    (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume).IsMulRightInvariant := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let μ := Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume
  let : μ.IsHaarMeasure := exponential_basis_measure_isHaar haar e hnil Exp hExp b
  obtain ⟨⟨chart, hc⟩, _⟩ := haar.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)
  apply isMulRightInvariant_map_of_neg volume _
    (continuous_exponential_basis e Exp chart hc b).measurable
  intro x
  simp only [Function.comp_apply, map_neg, hExp.map_neg]

end PolycyclicRecognition

end

end OAI
