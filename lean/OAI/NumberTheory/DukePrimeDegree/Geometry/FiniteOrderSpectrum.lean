import OAI.NumberTheory.PrimePackets.PermutationArtin

namespace OAI

/-!
# Spectral data for finite-order Artin operators

The local permutation and monomial operators have finite order. Their
eigenbases express both traces and Euler determinants using the same
finite list of eigenvalues.
-/

noncomputable section
open Module
open scoped BigOperators Classical Polynomial

namespace DukePrimeDegree

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_eigenbasis_of_finite_order (T : Module.End ℂ V)
    {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℂ V) (lam : Fin n → ℂ),
      ∀ i, T (b i) = lam i • b i := by
  have hss : T.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := Polynomial.X ^ m - 1)
    · exact (Polynomial.X_pow_sub_one_separable_iff.mpr
        (by exact_mod_cast hm.ne' : (m : ℂ) ≠ 0)).squarefree
    · simpa using sub_eq_zero.mpr hT
  have hi : DirectSum.IsInternal T.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  have hi' : DirectSum.IsInternal (fun μ : T.Eigenvalues => T.eigenspace μ.val) :=
    (DirectSum.isInternal_ne_bot_iff).mpr hi
  let b := hi'.collectedBasis (fun μ => Module.finBasis ℂ (T.eigenspace μ.val))
  let I := (μ : T.Eigenvalues) × Fin (finrank ℂ (T.eigenspace μ.val))
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, b.reindex e, fun i => (e.symm i).1.val, ?_⟩
  intro i
  apply Module.End.mem_eigenspace_iff.mp
  simpa only [Basis.reindex_apply, b] using
    hi'.collectedBasis_mem (fun μ => Module.finBasis ℂ (T.eigenspace μ.val)) (e.symm i)

omit [FiniteDimensional ℂ V] in
theorem trace_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (T : Module.End ℂ V) (lam : ι → ℂ)
    (hT : ∀ i, T (b i) = lam i • b i) :
    LinearMap.trace ℂ V T = ∑ i, lam i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  have he : LinearMap.toMatrix b b T = Matrix.diagonal lam := by
    ext i j
    rw [LinearMap.toMatrix_apply', hT j, map_smul]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [he, Matrix.trace_diagonal]

omit [FiniteDimensional ℂ V] in
theorem trace_pow_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (T : Module.End ℂ V) (lam : ι → ℂ)
    (hT : ∀ i, T (b i) = lam i • b i) (k : ℕ) :
    LinearMap.trace ℂ V (T ^ k) = ∑ i, lam i ^ k := by
  apply trace_eq_sum_of_eigenbasis b
  intro i
  exact (show T.HasEigenvector (lam i) (b i) from
    ⟨Module.End.mem_eigenspace_iff.mpr (hT i), b.ne_zero i⟩).pow_apply k

omit [FiniteDimensional ℂ V] in
theorem euler_det_eq_prod_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (T : Module.End ℂ V) (lam : ι → ℂ)
    (hT : ∀ i, T (b i) = lam i • b i) (z : ℂ) :
    (LinearMap.id - z • T).det = ∏ i, (1 - z * lam i) := by
  apply PrimeDegreePackets.GaloisIdealCharacter.det_eq_prod_of_eigenbasis b
  intro i
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    hT, smul_smul, sub_smul, one_smul]

end DukePrimeDegree

end

end OAI
