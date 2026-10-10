import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledGeneratorBounds

namespace OAI

/-! # Exponential bounds for actual finite word expansions

The maximizing-basis exchange estimate controls every word in the finite
list. A common surplus or deficit in the coefficients passes to the norm
of the whole sum, uniformly over the selected maximizing basis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- All words, rather than just the original letters, have uniformly bounded
coordinates after normalization by their own weight. -/
theorem exists_uniform_rescaled_word_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (cost : S → ℝ) (β : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀) cost β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ w : S,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => cost (β.val j)) r).equivFun
          (Real.exp (r * cost w) • evalBracketWord X w)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound
    (wordListCoordinates X S b₀)
  refine ⟨C, hC, ?_⟩
  intro cost β hβ r hr w
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  change |(exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => cost (β.val j)) r).repr
      (Real.exp (r * cost w) • evalBracketWord X w) j| ≤ C
  rw [repr_exponentialRescaleBasis_smul]
  have h := hb cost β.val hβ w j r hr
  rw [columnCoordinates_eq_wordBasis_repr X S b₀ β] at h
  exact h

/-- A finite expansion with a common exponential margin retains that margin
in the actual normalized coordinate norm. The index may repeat words. -/
theorem norm_rescaled_word_sum_le
    {J : Type*} [Fintype J]
    (X : I → L) (S : Finset (FreeMagma I))
    (b : Basis (Fin (finrank ℝ L)) ℝ L)
    (cost : S → ℝ) (r : ℝ) {C R θ : ℝ} (hR : 0 ≤ R)
    (hword : ∀ w : S, ‖b.equivFun
      (Real.exp (r * cost w) • evalBracketWord X w)‖ ≤ C)
    (w : J → S) (a : J → ℝ)
    (ha : ∀ j, |a j| ≤ R * Real.exp (r * (cost (w j) + θ))) :
    ‖b.equivFun (∑ j, a j • evalBracketWord X (w j))‖ ≤
      (Fintype.card J : ℝ) * C * R * Real.exp (r * θ) := by
  have hcoef (j : J) : |a j * Real.exp (-(r * cost (w j)))| ≤
      R * Real.exp (r * θ) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (R * Real.exp (r * (cost (w j) + θ))) *
          Real.exp (-(r * cost (w j))) :=
        mul_le_mul_of_nonneg_right (ha j) (Real.exp_pos _).le
      _ = R * Real.exp (r * θ) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hterm (j : J) : ‖b.equivFun (a j • evalBracketWord X (w j))‖ ≤
      C * R * Real.exp (r * θ) := by
    have he : a j • evalBracketWord X (w j) =
        (a j * Real.exp (-(r * cost (w j)))) •
          (Real.exp (r * cost (w j)) • evalBracketWord X (w j)) := by
      rw [smul_smul, mul_assoc, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, mul_one]
    rw [he, map_smul, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (R * Real.exp (r * θ)) * C :=
        mul_le_mul (hcoef j) (hword (w j)) (norm_nonneg _)
          (mul_nonneg hR (Real.exp_pos _).le)
      _ = _ := by ring
  rw [map_sum]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring))

end PolycyclicRecognition

end

end OAI
