import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledImageVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Rescaled exponential image volume along profile sequences -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold Topology ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- The subexponential logarithmic image loss survives the rescaled
exponential chart with exactly the selected word-basis exponent. -/
theorem rescaled_image_volume_lower_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {I : Type*} (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (C : ℕ → Set (Fin (finrank ℝ L) → ℝ))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun n => (volume (C n)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
        ((((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
          (fun j => cost (β.val j)) (scale n)).equivFun.symm)) '' C n)).toReal /
        Real.exp (scale n * columnBasisWeight cost β.val)) := by
  have hdet : 0 < |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| :=
    abs_pos.mpr (wordBasis_det_ne_zero X words b₀ β)
  have he (n : ℕ) :
      ((Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
        ((((Exp ∘ e) ∘ (exponentialRescaleBasis (WordBasisSelections.basis X words β)
          (fun j => cost (β.val j)) (scale n)).equivFun.symm)) '' C n)).toReal /
        Real.exp (scale n * columnBasisWeight cost β.val) =
      |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det| * (volume (C n)).toReal := by
    rw [exponential_rescaled_subset_measure e Exp chart hchart X words b₀ β cost (scale n) (C n)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (Real.exp_pos _).le]
    field_simp
  have hc : HasSubexponentialLowerBoundSeq scale (fun _ =>
      |(columnBasisMatrix (wordListCoordinates X words b₀) β.val).det|) := by
    simpa only [Function.comp_def] using (subexponential_lower_const hdet).along_sequence hscale
  have hh := hc.mul hlower
  convert hh using 1
  funext n
  exact he n

end PolycyclicRecognition

end

end OAI
