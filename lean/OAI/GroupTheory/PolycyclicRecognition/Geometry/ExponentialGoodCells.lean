import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TranslatedBoxMass
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Relative mass is unchanged by the actual translated exponential chart -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] [SimplyConnectedSpace G] in
/-- The translated exponential coordinate map preserves Borel measurability
of every independently selected good subset. -/
theorem measurableEmbedding_translated_exponential_basis
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b : Basis (Fin n) ℝ L) (k : G) :
    MeasurableEmbedding (fun y => ((Exp ∘ e) ∘ b.equivFun.symm) y * k) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let b' := b.map e.toLinearEquiv
  let c : (Fin n → ℝ) ≃ₜ G :=
    b'.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have he : ((Exp ∘ e) ∘ b.equivFun.symm) = c := by
    funext y
    dsimp only [c, Function.comp_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv]
    rw [hchart, Basis.map_equivFun]
    rfl
  rw [he]
  exact (MeasurableEquiv.mulRight k).measurableEmbedding.comp c.measurableEmbedding

/-- Both the good set and the original cell acquire exactly the same
Jacobian, including the deterministic right suffix. No density estimate is
lost when the independently sampled coordinate good set is put in the group. -/
theorem translated_exponential_cell_ratio
    (haar : NilpotentExponentialHaarInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (r : ℝ) (k : G)
    (A Q : Set (Fin (finrank ℝ L) → ℝ)) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    let f := fun y => ((Exp ∘ e) ∘ (exponentialRescaleBasis
      (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm) y * k
    (μ (f '' A)).toReal / (μ (f '' Q)).toReal = (volume A).toReal / (volume Q).toReal := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haar e hnil Exp hExp b₀
  let g := (Exp ∘ e) ∘ (exponentialRescaleBasis
    (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) r).equivFun.symm
  have himage (S : Set (Fin (finrank ℝ L) → ℝ)) :
      (fun y => g y * k) '' S = (fun y : G => y * k) '' (g '' S) :=
    image_comp (fun y : G => y * k) g S
  have hm (S : Set (Fin (finrank ℝ L) → ℝ)) :
      (μ ((fun y => g y * k) '' S)).toReal =
        (|(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| *
          Real.exp (r * columnBasisWeight cost β.val)) * (volume S).toReal := by
    rw [himage, measure_image_mul_right μ]
    dsimp only [μ, g]
    rw [exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost r S]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (Real.exp_pos _).le]
  dsimp only
  change (μ ((fun y => g y * k) '' A)).toReal /
    (μ ((fun y => g y * k) '' Q)).toReal = _
  rw [hm, hm, mul_div_mul_left]
  exact mul_ne_zero (abs_ne_zero.mpr (wordBasis_det_ne_zero X words b₀ β)) (Real.exp_ne_zero _)

end PolycyclicRecognition

end

end OAI
