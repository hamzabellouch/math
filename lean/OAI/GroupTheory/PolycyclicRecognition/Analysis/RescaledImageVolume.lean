import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSubsetVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialBounds
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # Accessible logarithmic volume becomes the exact exponential Haar rate -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Continuity is obtained from the supplied intrinsic exponential chart. -/
theorem continuous_exponential_basis {n : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (b : Basis (Fin n) ℝ L) : Continuous (((Exp ∘ e) ∘ b.equivFun.symm) : (Fin n → ℝ) → G) := by
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
  exact c.continuous

/-- The subexponential logarithmic image loss survives the rescaled
exponential chart with exactly the selected word-basis exponent. -/
theorem rescaled_image_volume_lower
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {I : Type*} (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (C : ℝ → Set (Fin (finrank ℝ L) → ℝ))
    (hlower : HasSubexponentialLowerBound (fun r => (volume (C r)).toReal)) :
    HasSubexponentialLowerBound (fun r =>
      ((Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
        ((((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
          (fun j => cost (β.val j)) r).equivFun.symm)) '' C r)).toReal /
        Real.exp (r * columnBasisWeight cost β.val)) := by
  have hdet : 0 < |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| :=
    abs_pos.mpr (wordBasis_det_ne_zero X words b₀ β)
  have he (r : ℝ) :
      ((Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
        ((((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
          (fun j => cost (β.val j)) r).equivFun.symm)) '' C r)).toReal /
        Real.exp (r * columnBasisWeight cost β.val) =
      |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| * (volume (C r)).toReal := by
    rw [exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost r (C r)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (Real.exp_pos _).le]
    field_simp
  simpa only [he] using (subexponential_lower_const hdet).mul hlower

end PolycyclicRecognition

end

end OAI
