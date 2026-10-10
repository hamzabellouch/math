import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedBoxVolume

namespace OAI

/-! # Exponential boxes and the concrete weighted coordinate boxes

The sup-norm definition of a box agrees with the previously measured linear
image of a cube. This identifies group boxes with images of sets having the
exact determinant volume, without treating the two coordinate systems as an
extra hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped Matrix

variable {I L G : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- A single basis identifies its exponential box with the exponential
image of the standard coordinate cube. -/
theorem exponentialCoordinateBox_eq_cube_image {n : ℕ}
    (Exp : L → G) (b : Basis (Fin n) ℝ L) (R : ℝ) (hR : 0 ≤ R) :
    exponentialCoordinateBox Exp b R =
      (Exp ∘ b.equivFun.symm) '' Set.Icc (fun _ => -R) (fun _ => R) := by
  ext g
  rw [mem_exponentialCoordinateBox_iff Exp b R hR]
  constructor
  · rintro ⟨x, hx, hb⟩
    refine ⟨b.equivFun x, ?_, ?_⟩
    · exact ⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩
    · simpa only [Function.comp_apply, b.equivFun.symm_apply_apply] using hx
  · rintro ⟨t, ht, rfl⟩
    refine ⟨b.equivFun.symm t, rfl, fun i => ?_⟩
    have hi : |b.equivFun (b.equivFun.symm t) i| ≤ R := by
      rw [b.equivFun.apply_symm_apply]
      exact abs_le.mpr ⟨ht.1 i, ht.2 i⟩
    exact hi

/-- Matrix of the scaled word basis in the fixed ambient coordinates. -/
theorem scaledColumnMatrix_eq_basis_toMatrix
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X S)
    (cost : S → ℝ) (r : ℝ) :
    scaledColumnMatrix (wordListCoordinates X S b₀) cost β.val r =
      b₀.toMatrix (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun i => cost (β.val i)) r) := by
  ext i j
  simp only [scaledColumnMatrix, Basis.toMatrix_apply, exponentialRescaleBasis,
    Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, map_smul, Finsupp.smul_apply,
    smul_eq_mul, wordListCoordinates, Basis.equivFun_apply]
  exact congrArg (fun x : L => Real.exp (r * cost (β.val j)) * b₀.repr x i)
    (WordBasisSelections.eval_words X S β j)

/-- A basis sends its coordinate cube to exactly the vectors with bounded
coordinates, including dimension zero when `R` is nonnegative. -/
theorem basis_image_cube {n : ℕ} (b₀ b : Basis (Fin n) ℝ L)
    (R : ℝ) (hR : 0 ≤ R) :
    (Matrix.toLin' (b₀.toMatrix b)) '' Set.Icc (fun _ => -R) (fun _ => R) =
      b₀.equivFun '' {x : L | ‖b.equivFun x‖ ≤ R} := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨b.equivFun.symm t, ?_, ?_⟩
    · change ‖b.equivFun (b.equivFun.symm t)‖ ≤ R
      rw [b.equivFun.apply_symm_apply]
      apply (pi_norm_le_iff_of_nonneg hR).mpr
      intro i
      exact Real.norm_eq_abs (t i) ▸ abs_le.mpr ⟨ht.1 i, ht.2 i⟩
    · change b₀.equivFun (b.equivFun.symm t) = (b₀.toMatrix b) *ᵥ t
      have h := b.toMatrix_mulVec_repr b₀ (b.equivFun.symm t)
      simpa only [← Basis.equivFun_apply, b.equivFun.apply_symm_apply] using h.symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨b.equivFun x, ?_, ?_⟩
    · constructor <;> intro i
      · exact (abs_le.mp ((Real.norm_eq_abs _ ▸ norm_le_pi_norm (b.equivFun x) i).trans hx)).1
      · exact (abs_le.mp ((Real.norm_eq_abs _ ▸ norm_le_pi_norm (b.equivFun x) i).trans hx)).2
    · exact b.toMatrix_mulVec_repr b₀ x

/-- The group box is the exponential image of the exact weighted coordinate
box used by the determinant-volume theorem. -/
theorem exponentialCoordinateBox_eq_weighted_image
    (X : I → L) (S : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X S)
    (cost : S → ℝ) (r R : ℝ) (hR : 0 ≤ R) (Exp : L → G) :
    exponentialCoordinateBox Exp
      (exponentialRescaleBasis (WordBasisSelections.basis X S β)
        (fun i => cost (β.val i)) r) R =
    (Exp ∘ b₀.equivFun.symm) '' weightedCoordinateBox
      (wordListCoordinates X S b₀) cost β.val r R := by
  rw [weightedCoordinateBox, scaledColumnMatrix_eq_basis_toMatrix,
    basis_image_cube _ _ R hR, ← Set.image_comp]
  ext g
  simp only [exponentialCoordinateBox, Set.mem_ofPred_eq, Set.mem_image,
    Function.comp_apply, b₀.equivFun.symm_apply_apply]
  constructor
  · rintro ⟨x, hx, hb⟩
    exact ⟨x, hb, hx⟩
  · rintro ⟨x, hb, hx⟩
    exact ⟨x, hx, hb⟩

end PolycyclicRecognition

end

end OAI
