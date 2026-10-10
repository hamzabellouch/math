import OAI.NumberTheory.DukePrimeDegree.Geometry.PairedCoordinateAlgebra
import OAI.NumberTheory.DukePrimeDegree.Dynamics.GenericRootCommutant

namespace OAI

/-!
# The scalar commutant forced by an opposite root pair

The paired-coordinate algebra applies to the rational matrices conjugated
by a lattice representative. The rational structure is
transported through the matrix identity, rather than postulated. A finite
invariant orbit and one opposite root pair then force its rational
stabilizer commutant to consist of scalars.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma transpose_conjugate_rational_preserves_rowSpace {n : ℕ}
    (g : G n) (B : Matrix (Fin n) (Fin n) ℚ) :
    ∀ w ∈ rationalRowSpace g,
      (slMatrixConjugation g (rationalMatrixCast B))ᵀ *ᵥ w ∈ rationalRowSpace g := by
  rintro w ⟨z, rfl⟩
  refine ⟨z ᵥ* B, ?_⟩
  have hg : g.val * g⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hconj : g.val * slMatrixConjugation g (rationalMatrixCast B) =
      rationalMatrixCast B * g.val := by
    simp only [slMatrixConjugation, ← mul_assoc, hg, one_mul]
  have hcast : (fun k => ((z ᵥ* B) k : ℝ)) =
      (fun k => (z k : ℝ)) ᵥ* rationalMatrixCast B := by
    ext k
    simp [Matrix.vecMul, dotProduct, rationalMatrixCast_apply]
  rw [rationalRowMap_apply, Matrix.mulVec_transpose, rationalRowMap_apply, hcast,
    Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul]

lemma transpose_mulVec_coordinate_of_column {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (hcol : ∀ a, a ≠ i → M a i = 0) (v : Fin n → ℝ) :
    (Mᵀ *ᵥ v) i = M i i * v i := by
  rw [Matrix.mulVec_transpose]
  change (∑ a, v a * M a i) = _
  rw [Finset.sum_eq_single i]
  · exact mul_comm _ _
  · intro a _ hai
    rw [hcol a hai, mul_zero]
  · simp

lemma equal_diagonal_of_commute_root {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (h : Commute M (Matrix.transvection i j (1 : ℝ))) : M i i = M j j := by
  have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) h.eq
  simp only [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
    one_mul] at he
  exact add_left_cancel he

lemma slMatrixConjugation_smul_one {n : ℕ} (g : G n) (c : ℝ) :
    slMatrixConjugation g (c • (1 : Matrix (Fin n) (Fin n) ℝ)) = c • 1 := by
  simp only [slMatrixConjugation, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

/-- A conjugated rational matrix whose two indicated columns have a common
scalar eigenvalue must itself be a rational scalar matrix. -/
theorem rationalMatrix_scalar_of_opposite_roots {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (B : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) (hij : i ≠ j)
    (hijB : Commute (slMatrixConjugation g (rationalMatrixCast B))
      (Matrix.transvection i j (1 : ℝ)))
    (hjiB : Commute (slMatrixConjugation g (rationalMatrixCast B))
      (Matrix.transvection j i (1 : ℝ))) :
    ∃ q : ℚ, B = q • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  let M := slMatrixConjugation g (rationalMatrixCast B)
  have hcol_i := offColumn_zero_of_commute_root M i j hijB
  have hcol_j := offColumn_zero_of_commute_root M j i hjiB
  have hdiag := equal_diagonal_of_commute_root M i j hijB
  have hmem : (M i i, Mᵀ) ∈ pairedCoordinateAlgebra (rationalRowSpace g) i j := by
    refine ⟨transpose_conjugate_rational_preserves_rowSpace g B, ?_, ?_⟩
    · exact transpose_mulVec_coordinate_of_column M i hcol_i
    · intro v
      rw [transpose_mulVec_coordinate_of_column M j hcol_j, ← hdiag]
  rw [rationalRowSpace_pairedCoordinateAlgebra_eq_bot hn g hgeneric i j hij] at hmem
  obtain ⟨q, hq⟩ := Algebra.mem_bot.mp hmem
  have hmat : M = (q : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have ht : algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q = Mᵀ :=
      congrArg (fun a : ℝ × Matrix (Fin n) (Fin n) ℝ => a.2) hq
    have hscalar : algebraMap ℚ (Matrix (Fin n) (Fin n) ℝ) q =
        (q : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext a b
      by_cases hab : a = b <;>
        simp [Algebra.algebraMap_eq_smul_one, Rat.smul_def, hab]
    rw [hscalar] at ht
    have ht' := congrArg Matrix.transpose ht
    simpa only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose]
      using ht'.symm
  have hcast : rationalMatrixCast B = (q : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have he := congrArg (slMatrixConjugation g⁻¹) hmat
    have hinverse : slMatrixConjugation g⁻¹ M = rationalMatrixCast B := by
      simpa only [M, inv_inv] using slMatrixConjugation_inverse g⁻¹ (rationalMatrixCast B)
    rw [hinverse, slMatrixConjugation_smul_one] at he
    exact he
  refine ⟨q, ?_⟩
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℚ ℝ)
  change rationalMatrixCast B = rationalMatrixCast (q • (1 : Matrix (Fin n) (Fin n) ℚ))
  rw [hcast]
  ext a b
  by_cases hab : a = b <;> simp [rationalMatrixCast_apply, hab]

/-- Actual finite-orbit specialization: both opposite roots are members of
the orbit group; polynomial recurrence supplies commutation with each. -/
theorem rationalStabilizer_scalar_of_finite_opposite_root_orbit {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot_ij : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (hroot_ji : Matrix.SpecialLinearGroup.transvection hij.symm (1 : ℝ) ∈ L)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) :
    ∃ q : ℚ, B = q • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  have hM : ∀ s : pointOrbitStabilizer g L,
      Commute (slMatrixConjugation g (rationalMatrixCast B)) s.val.val := by
    intro s
    obtain ⟨γ, hγ⟩ := pointOrbitStabilizer_eq_conjugate g L s
    rw [← hγ]
    exact ((commute_rationalMatrixCast_iff B (latticeStabilizerMatrix g L γ)).mpr
      ((mem_commutatorFamily_ker _ _).mp hB γ)).map (slMatrixConjugationHom g)
  exact rationalMatrix_scalar_of_opposite_roots hn g hgeneric B i j hij
    (commute_root_of_finite_root_orbit g L μ hμ hinv i j hij hroot_ij _ hM)
    (commute_root_of_finite_root_orbit g L μ hμ hinv j i hij.symm hroot_ji _ hM)

end DukePrimeDegree

end

end OAI
