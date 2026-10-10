import OAI.GroupTheory.PolycyclicRecognition.Analysis.TupleMeasureScaling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSubsetVolume

namespace OAI

/-! # Exact product volume under independent exponential coordinate charts -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal NNReal BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

def basisVolumeMultiplier {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) : ℝ≥0 :=
  ⟨|(b₀.toMatrix b).det|, abs_nonneg _⟩

def exponentialBasisHomeomorph {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (b : Basis (Fin n) ℝ L) :
    (Fin n → ℝ) ≃ₜ G :=
  (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart

omit [MeasurableSpace G] [BorelSpace G] in
theorem exponentialBasisHomeomorph_apply {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Basis (Fin n) ℝ L) (x : Fin n → ℝ) :
    exponentialBasisHomeomorph e chart b x = Exp (e (b.equivFun.symm x)) := hchart _

theorem map_exponentialBasisHomeomorph_inverse {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ b : Basis (Fin n) ℝ L) :
    Measure.map (exponentialBasisHomeomorph e chart b).symm
      (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume) =
        basisVolumeMultiplier b₀ b • (volume : Measure (Fin n → ℝ)) := by
  ext S hS
  rw [Measure.map_apply (exponentialBasisHomeomorph e chart b).symm.measurable hS,
    Measure.smul_apply]
  have hpre : (exponentialBasisHomeomorph e chart b).symm ⁻¹' S =
      ((Exp ∘ e) ∘ b.equivFun.symm) '' S := by
    rw [(exponentialBasisHomeomorph e chart b).preimage_symm]
    congr 1
    funext x
    exact exponentialBasisHomeomorph_apply e Exp chart hchart b x
  rw [hpre, exponential_basis_subset_measure e Exp chart hchart]
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
  rfl

theorem map_exponential_tuple_coordinates {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin n) ℝ L) (b : Fin h → Basis (Fin n) ℝ L) :
    Measure.map (fun u i => (exponentialBasisHomeomorph e chart (b i)).symm (u i))
      (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) =
        (∏ i, basisVolumeMultiplier b₀ (b i)) •
          (volume : Measure (Fin h → Fin n → ℝ)) := by
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  have he : ((Exp ∘ e) ∘ b₀.equivFun.symm) = exponentialBasisHomeomorph e chart b₀ := by
    funext x
    exact (exponentialBasisHomeomorph_apply e Exp chart hchart b₀ x).symm
  let : SigmaFinite μ := by
    dsimp only [μ]
    rw [he]
    exact (exponentialBasisHomeomorph e chart b₀).measurableEmbedding.sigmaFinite_map
  exact map_pi_of_coordinate_scaling (fun _ : Fin h => μ) (fun _ : Fin h => volume)
    (fun i => (exponentialBasisHomeomorph e chart (b i)).symm)
    (fun i => (exponentialBasisHomeomorph e chart (b i)).symm.measurable)
    (fun i => basisVolumeMultiplier b₀ (b i))
    (fun i => map_exponentialBasisHomeomorph_inverse e Exp chart hchart b₀ (b i))

def exponentialTupleCoordinates {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (b : Fin h → Basis (Fin n) ℝ L) : (Fin h → G) ≃ₜ (Fin h → Fin n → ℝ) :=
  Homeomorph.piCongrRight (fun i => (exponentialBasisHomeomorph e chart (b i)).symm)

theorem exponential_tuple_subset_measure {n h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ : Basis (Fin n) ℝ L) (b : Fin h → Basis (Fin n) ℝ L) (S : Set (Fin h → G)) :
    (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) S =
      ENNReal.ofReal (∏ i, |(b₀.toMatrix (b i)).det|) *
        volume (exponentialTupleCoordinates e chart b '' S) := by
  let : SecondCountableTopology G := (exponentialBasisHomeomorph e chart b₀).symm.secondCountableTopology
  let f := exponentialTupleCoordinates e chart b
  have hm := map_exponential_tuple_coordinates e Exp chart hchart b₀ b
  change Measure.map f _ = _ at hm
  have hv := congrArg (fun μ : Measure (Fin h → Fin n → ℝ) => μ (f '' S)) hm
  rw [f.measurableEmbedding.map_apply, Set.preimage_image_eq _ f.injective,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hv
  rw [hv]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  exact map_prod NNReal.toRealHom (fun i => basisVolumeMultiplier b₀ (b i)) Finset.univ

end PolycyclicRecognition

end

end OAI
