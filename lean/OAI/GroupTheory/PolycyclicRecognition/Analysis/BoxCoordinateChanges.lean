import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBoxComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RescaledLieFamily

namespace OAI

/-! # Coordinate changes between the individual and union boxes

The target normalization uses a maximizing word basis. Inclusion of the
individual support costs gives a uniform bound on the coordinate change.
When a letter attains the union support on one side, its two normalized
vectors correspond exactly under this map.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem bracketWordExponent_mono [Fintype I] [DecidableEq I]
    {s t : I → ℝ} (h : ∀ i, s i ≤ t i) (w : FreeMagma I) :
    bracketWordExponent s w ≤ bracketWordExponent t w := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg _))

def boxCoordinateChange {n : ℕ} (target source : Basis (Fin n) ℝ L) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (source.equivFun.symm.trans target.equivFun).toLinearMap.toContinuousLinearMap

@[simp] theorem boxCoordinateChange_apply {n : ℕ}
    (target source : Basis (Fin n) ℝ L) (v : Fin n → ℝ) :
    boxCoordinateChange target source v = target.equivFun (source.equivFun.symm v) := rfl

@[simp] theorem boxCoordinateChange_coordinates {n : ℕ}
    (target source : Basis (Fin n) ℝ L) (v : L) :
    boxCoordinateChange target source (source.equivFun v) = target.equivFun v := by
  simp

theorem exists_uniform_boxCoordinateChange_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (cost newCost : S → ℝ)
      (β γ : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ {r : ℝ}, 0 ≤ r → (∀ w, newCost w ≤ cost w) →
        ‖boxCoordinateChange
          (exponentialRescaleBasis (WordBasisSelections.basis X S β)
            (fun j => cost (β.val j)) r)
          (exponentialRescaleBasis (WordBasisSelections.basis X S γ)
            (fun j => newCost (γ.val j)) r)‖ ≤ D := by
  obtain ⟨D, hD, hbound⟩ := exists_word_box_comparison_constant X S b₀
  refine ⟨D, hD, ?_⟩
  intro cost newCost β γ hβ r hr hc
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro v
  have h := hbound cost newCost β γ hβ (ε := 0) hr (by simpa using hc)
    ((exponentialRescaleBasis (WordBasisSelections.basis X S γ)
      (fun j => newCost (γ.val j)) r).equivFun.symm v)
  simpa only [boxCoordinateChange_apply, LinearEquiv.apply_symm_apply,
    zero_mul, Real.exp_zero, mul_one] using h

theorem rescaled_generator_in_coordinate_image
    [Fintype I] [DecidableEq I]
    (X : I → L) (S : Finset (FreeMagma I))
    (β γ : WordBasisSelections X S) (s t : I → ℝ) (r : ℝ) (i : I)
    (hi : s i = t i) :
    boxCoordinateChange
      (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent s (β.val j)) r)
      (exponentialRescaleBasis (WordBasisSelections.basis X S γ)
        (fun j => bracketWordExponent t (γ.val j)) r)
      ((rescaledLieData X S γ t r).2 i) = (rescaledLieData X S β s r).2 i := by
  simp only [rescaledLieData, boxCoordinateChange_coordinates, hi]

end PolycyclicRecognition

end

end OAI
