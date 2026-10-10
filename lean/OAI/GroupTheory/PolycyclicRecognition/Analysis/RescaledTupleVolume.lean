import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTupleCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Exact normalization of correlated tuple volume

The domain is an arbitrary tuple set. Its coordinates need not be
independent after the successful parameters have been retained.
-/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set Filter
open scoped Manifold ENNReal Topology BigOperators

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

def rescaledTupleBases {h : ℕ} (X : I → L) (words : Finset (FreeMagma I))
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ) (r : ℝ) :=
  fun i => exponentialRescaleBasis (WordBasisSelections.basis X words (β i))
    (fun j => cost i ((β i).val j)) r

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem exponential_rescaled_tuple_subset_measure {h : ℕ}
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (r : ℝ) (S : Set (Fin h → G)) :
    (Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) S =
      ENNReal.ofReal (∏ i, |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det|) *
        ENNReal.ofReal (Real.exp (r * ∑ i, columnBasisWeight (cost i) (β i).val)) *
        volume (exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost r) '' S) := by
  rw [exponential_tuple_subset_measure e Exp chart hchart b₀
    (rescaledTupleBases X words β cost r) S]
  have hd (i : Fin h) : |(b₀.toMatrix (rescaledTupleBases X words β cost r i)).det| =
      |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det| *
        Real.exp (r * columnBasisWeight (cost i) (β i).val) := by
    change |(b₀.toMatrix (exponentialRescaleBasis
      (WordBasisSelections.basis X words (β i))
      (fun j => cost i ((β i).val j)) r)).det| = _
    rw [← scaledColumnMatrix_eq_basis_toMatrix, det_scaledColumnMatrix,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_comm _ _
  rw [Finset.prod_congr rfl (fun i _ => hd i)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum,
    ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => abs_nonneg _)), mul_assoc]

theorem rescaled_tuple_volume_lower_sequence {h : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (S : ℕ → Set (Fin h → G))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)) (S n)).toReal /
        Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val))) :
    HasSubexponentialLowerBoundSeq scale (fun n =>
      (volume (exponentialTupleCoordinates e chart
        (rescaledTupleBases X words β cost (scale n)) '' S n)).toReal) := by
  let d := ∏ i, |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det|
  have hd : 0 < d := Finset.prod_pos (fun i _ => abs_pos.mpr (wordBasis_det_ne_zero X words b₀ (β i)))
  have he (n : ℕ) :
      (((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume))
        (S n)).toReal / Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val)) / d =
      (volume (exponentialTupleCoordinates e chart
        (rescaledTupleBases X words β cost (scale n)) '' S n)).toReal := by
    rw [exponential_rescaled_tuple_subset_measure e Exp chart hchart X words b₀ β cost (scale n) (S n)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    field_simp
  have h := hlower.div (sequence_subexponential_upper_const hscale d)
    (Eventually.of_forall (fun _ => hd))
  simpa only [he] using h


theorem rescaled_tuple_image_volume_lower_sequence {h : ℕ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : Fin h → WordBasisSelections X words) (cost : Fin h → words → ℝ)
    (C : ℕ → Set (Fin h → Fin (finrank ℝ L) → ℝ))
    (hlower : HasSubexponentialLowerBoundSeq scale (fun n => (volume (C n)).toReal)) :
    HasSubexponentialLowerBoundSeq scale (fun n =>
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume))
        ((exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).symm '' C n)).toReal /
          Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val)) := by
  let d := ∏ i, |(columnBasisMatrix (wordListCoordinates X words b₀) (β i).val).det|
  have hd : 0 < d := Finset.prod_pos (fun i _ => abs_pos.mpr (wordBasis_det_ne_zero X words b₀ (β i)))
  have he (n : ℕ) :
      ((Measure.pi (fun _ : Fin h => Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume))
        ((exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).symm '' C n)).toReal /
          Real.exp (scale n * ∑ i, columnBasisWeight (cost i) (β i).val) = d * (volume (C n)).toReal := by
    rw [exponential_rescaled_tuple_subset_measure e Exp chart hchart X words b₀ β cost (scale n)]
    have hi : exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n)) ''
        ((exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).symm '' C n) = C n := by
      exact (exponentialTupleCoordinates e chart (rescaledTupleBases X words β cost (scale n))).image_symm_image (C n)
    rw [hi, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    field_simp
  simpa only [he] using (sequence_subexponential_lower_const hscale hd).mul hlower

end PolycyclicRecognition

end

end OAI
