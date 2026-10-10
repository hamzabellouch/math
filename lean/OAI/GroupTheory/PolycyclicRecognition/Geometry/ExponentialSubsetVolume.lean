import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # Volume of arbitrary subsets in rescaled exponential coordinates

The change-of-coordinates determinant formula applies to the independently
sampled good subset, not just to an entire box. The exponential chart is a
measurable embedding, so this calculation does not assume absolute
continuity of an arbitrarily selected word parametrization.
-/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {I : Type*} {n : ℕ}

/-- Change of exponential basis on an arbitrary coordinate set. -/
theorem exponential_basis_image_eq
    {G : Type*} (Exp : L → G) (b₀ b : Basis (Fin n) ℝ L) (S : Set (Fin n → ℝ)) :
    (Exp ∘ b.equivFun.symm) '' S =
      (Exp ∘ b₀.equivFun.symm) '' ((Matrix.toLin' (b₀.toMatrix b)) '' S) := by
  have hf : (Exp ∘ b.equivFun.symm) =
      (Exp ∘ b₀.equivFun.symm) ∘ (Matrix.toLin' (b₀.toMatrix b)) := by
    funext y
    have he := b.toMatrix_mulVec_repr b₀ (b.equivFun.symm y)
    rw [← Basis.equivFun_apply, b.equivFun.apply_symm_apply] at he
    dsimp only [Function.comp_apply]
    change (Matrix.toLin' (b₀.toMatrix b)) y = b₀.equivFun (b.equivFun.symm y) at he
    rw [he, b₀.equivFun.symm_apply_apply]
  rw [hf, Set.image_comp]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- The exact determinant formula for every coordinate subset in the global
nilpotent exponential chart. -/
theorem exponential_basis_subset_measure
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b₀ b : Basis (Fin n) ℝ L) (S : Set (Fin n → ℝ)) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (((Exp ∘ e) ∘ b.equivFun.symm) '' S) =
      ENNReal.ofReal |(b₀.toMatrix b).det| * volume S := by
  let b' := b₀.map e.toLinearEquiv
  let f := (Exp ∘ e) ∘ b₀.equivFun.symm
  let c : (Fin n → ℝ) ≃ₜ G :=
    b'.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : f = c := by
    funext y
    dsimp only [f, c, Function.comp_apply, Homeomorph.trans_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, LinearEquiv.coe_toContinuousLinearEquiv]
    rw [hchart, Basis.map_equivFun]
    rfl
  have hmeas : MeasurableEmbedding f := by rw [hf]; exact c.measurableEmbedding
  rw [exponential_basis_image_eq (Exp ∘ e) b₀ b S]
  change (Measure.map f volume) (f '' _) = _
  rw [hmeas.map_apply, Set.preimage_image_eq _ hmeas.injective,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin']

/-- The full exponential determinant remains valid after discarding any
bad coordinate subset from the independently sampled domain. -/
theorem exponential_rescaled_subset_measure
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (r : ℝ) (S : Set (Fin (finrank ℝ L) → ℝ)) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
        (fun j => cost (β.val j)) r).equivFun.symm) '' S) =
      ENNReal.ofReal |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| *
        ENNReal.ofReal (Real.exp (r * columnBasisWeight cost β.val)) * volume S := by
  rw [exponential_basis_subset_measure e Exp chart hchart,
    ← scaledColumnMatrix_eq_basis_toMatrix, det_scaledColumnMatrix, abs_mul,
    abs_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

end PolycyclicRecognition

end

end OAI
