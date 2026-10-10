import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxRadiusVolume
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

/-! # Exact radius ratios for every normalization of nilpotent Haar measure -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory MeasureTheory.Measure
open scoped Manifold ENNReal

variable {L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

/-- Dilating a coordinate box by a scalar changes its Haar volume by the
scalar to the dimension, independently of the exponential scaling basis. -/
theorem haar_exponential_box_radius
    (haarInput : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) (μ : Measure G) [μ.IsHaarMeasure]
    {R : ℝ} (hR : 0 ≤ R) :
    μ (exponentialCoordinateBox (Exp ∘ e) b R) =
      ENNReal.ofReal R ^ n * μ (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, E))
  let ν := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  let : ν.IsHaarMeasure := exponential_basis_measure_isHaar haarInput e hnil Exp hExp b₀
  obtain ⟨⟨chart, hc⟩, _⟩ := haarInput.2 Exp hExp (e.nilpotent_iff_equiv_nilpotent.mp hnil)
  have hv := exponential_box_radius_volume e Exp chart hc b₀ b hR
  have he := isMulLeftInvariant_eq_smul μ ν
  rw [he, Measure.smul_apply, Measure.smul_apply]
  change (haarScalarFactor μ ν : ℝ≥0∞) * ν (exponentialCoordinateBox (Exp ∘ e) b R) =
    ENNReal.ofReal R ^ n * ((haarScalarFactor μ ν : ℝ≥0∞) *
      ν (exponentialCoordinateBox (Exp ∘ e) b 1))
  rw [hv]
  ac_rfl

theorem haar_exponential_box_radius_real
    (haarInput : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) (μ : Measure G) [μ.IsHaarMeasure]
    {R : ℝ} (hR : 0 ≤ R) :
    μ.real (exponentialCoordinateBox (Exp ∘ e) b R) =
      R ^ n * μ.real (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  have h := congrArg ENNReal.toReal (haar_exponential_box_radius haarInput e hnil Exp hExp b₀ b μ hR)
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR] using h

end PolycyclicRecognition

end

end OAI
