import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure

namespace OAI

/-! # Inversion and right invariance of any nilpotent Haar normalization -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory MeasureTheory.Measure
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- Negation in exponential coordinates and uniqueness of Haar measure
prove inversion invariance for every Haar normalization. -/
theorem nilpotent_haar_isInvInvariant
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsInvInvariant := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, E))
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp hnil
  let b := Module.finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  let f := Exp ∘ b.equivFun.symm
  let ν := Measure.map f volume
  let : ν.IsHaarMeasure := hhaar _ b
  have hf : Measurable f := by
    have he : f = chart ∘ b.equivFun.symm := by
      funext x
      exact (hchart _).symm
    rw [he]
    exact (chart.continuous.comp b.equivFun.symm.toContinuousLinearEquiv.continuous).measurable
  let : ν.IsInvInvariant := isInvInvariant_map_of_neg volume f hf (by
    intro x
    simp only [f, Function.comp_apply, map_neg, hExp.map_neg])
  have heq : μ = haarScalarFactor μ ν • ν := isMulLeftInvariant_eq_smul μ ν
  constructor
  change Measure.map Inv.inv μ = μ
  calc
    Measure.map Inv.inv μ = Measure.map Inv.inv (haarScalarFactor μ ν • ν) :=
      congrArg (Measure.map Inv.inv) heq
    _ = haarScalarFactor μ ν • Measure.map Inv.inv ν :=
      Measure.map_smul _ measurable_inv.aemeasurable
    _ = haarScalarFactor μ ν • ν := by rw [map_inv_eq_self]
    _ = μ := heq.symm

/-- Inversion changes left Haar invariance into right invariance. -/
theorem nilpotent_haar_isMulRightInvariant
    (haar : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : μ.IsInvInvariant := nilpotent_haar_isInvInvariant haar Exp hExp hnil μ
  have hi : μ.inv = μ := Measure.inv_eq_self μ
  rw [← hi]
  infer_instance

end PolycyclicRecognition

end

end OAI
