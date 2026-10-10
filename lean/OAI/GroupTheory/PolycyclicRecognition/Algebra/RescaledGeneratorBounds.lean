import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedWordBrackets
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordModel

namespace OAI

/-! # Uniform bounds for normalized generator vectors

The same maximizing-basis exchange estimate which bounds structure constants
also bounds all exponentially rescaled generator vectors. Thus both parts of
the normalized Lie-law data lie in fixed bounded coordinate sets.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

/-- Coordinates of a scalar-rescaled vector in an exponentially rescaled basis. -/
theorem repr_exponentialRescaleBasis_smul {J : Type*} (b : Basis J ℝ L)
    (cost : J → ℝ) (r s : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b cost r).repr (Real.exp (r * s) • x) j =
      b.repr x j * Real.exp (r * (s - cost j)) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_mk0, Units.val_inv_eq_inv_val, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [← Real.exp_neg]
  have he : Real.exp (-(r * cost j)) * Real.exp (r * s) =
      Real.exp (r * (s - cost j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = b.repr x j * (Real.exp (-(r * cost j)) * Real.exp (r * s)) := by ring
    _ = _ := by rw [he]

/-- Uniform boundedness of all rescaled letters in every maximizing word basis. -/
theorem exists_uniform_rescaled_generator_bound
    (X : I → L) (S : Finset (FreeMagma I))
    (hS : ∀ i, FreeMagma.of i ∈ S) (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ) (β : WordBasisSelections X S),
      IsMaximizingColumnBasis (wordListCoordinates X S b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ i,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun
          (Real.exp (r * s i) • X i)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_normalized_coordinate_bound (wordListCoordinates X S b₀)
  refine ⟨C, hC, ?_⟩
  intro s β hβ r hr i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  change |(exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r).repr (Real.exp (r * s i) • X i) j| ≤ C
  rw [repr_exponentialRescaleBasis_smul]
  have hh := hb (fun w => bracketWordExponent s w) β.val hβ ⟨.of i, hS i⟩ j r hr
  rw [columnCoordinates_eq_wordBasis_repr X S b₀ β] at hh
  simpa only [bracketWordExponent_of, evalBracketWord_of, Basis.equivFun_apply] using hh

end PolycyclicRecognition

end

end OAI
