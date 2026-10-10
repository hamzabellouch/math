import OAI.NumberTheory.DukePrimeDegree.Dynamics.PairedRootCentralizer

namespace OAI

/-!
# Scalar real commutants of prime-degree finite root-pair orbits

Rationality of the actual lattice stabilizer's commutant turns the preceding
rational scalar theorem into a real scalar theorem. In particular, no
nontrivial real projection can commute with the orbit group. No orbit
existence is assumed beyond the finite invariant orbit explicitly supplied.
-/

noncomputable section
open Matrix Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def scalarMatrixSpace (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  (Algebra.linearMap ℝ (Matrix (Fin n) (Fin n) ℝ)).range

lemma mem_scalarMatrixSpace_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    M ∈ scalarMatrixSpace n ↔ ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  constructor
  · rintro ⟨c, hc⟩
    have he : c • (1 : Matrix (Fin n) (Fin n) ℝ) = M := by
      simpa only [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one] using hc
    exact ⟨c, he.symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, Algebra.algebraMap_eq_smul_one c⟩

/-- The full real commutant in integral lattice coordinates is scalar. -/
theorem realStabilizer_scalar_of_finite_opposite_root_orbit {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot_ij : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (hroot_ji : Matrix.SpecialLinearGroup.transvection hij.symm (1 : ℝ) ∈ L)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  apply (mem_scalarMatrixSpace_iff M).mp
  rw [latticeStabilizer_commutant_rational] at hM
  apply (Submodule.span_le.mpr ?_) hM
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨q, rfl⟩ := rationalStabilizer_scalar_of_finite_opposite_root_orbit
    hn g hgeneric L μ hμ hinv i j hij hroot_ij hroot_ji B hB
  apply (mem_scalarMatrixSpace_iff _).mpr
  refine ⟨(q : ℝ), ?_⟩
  change (q • (1 : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ) = _
  ext a b
  by_cases hab : a = b <;> simp [hab]

/-- The scalar conclusion in the actual orbit's real coordinates. -/
theorem pointStabilizer_scalar_of_finite_opposite_root_orbit {n : ℕ}
    (hn : n.Prime) (g : G n)
    (hgeneric : ∀ v ∈ rowLattice g.val, v ≠ 0 → ∀ k, v k ≠ 0)
    (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hinv : ∀ h : L, μ.map (fun x => latticeOrbitRightAction g L x h) = μ)
    (i j : Fin n) (hij : i ≠ j)
    (hroot_ij : Matrix.SpecialLinearGroup.transvection hij (1 : ℝ) ∈ L)
    (hroot_ji : Matrix.SpecialLinearGroup.transvection hij.symm (1 : ℝ) ∈ L)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨c, hc⟩ := realStabilizer_scalar_of_finite_opposite_root_orbit
    hn g hgeneric L μ hμ hinv i j hij hroot_ij hroot_ji
    (slMatrixConjugation g⁻¹ M) (inverseConjugate_mem_realStabilizer g L M hM)
  refine ⟨c, ?_⟩
  have he := congrArg (slMatrixConjugation g) hc
  rw [slMatrixConjugation_inverse, slMatrixConjugation_smul_one] at he
  exact he

end DukePrimeDegree

end

end OAI
