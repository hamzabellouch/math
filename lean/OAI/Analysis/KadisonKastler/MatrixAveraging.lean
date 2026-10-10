import OAI.Analysis.KadisonKastler.FiniteAveraging
import OAI.Analysis.KadisonKastler.SignedPermutation

namespace OAI

/-! # Averaging over a concrete finite matrix algebra

Signed permutation matrices give a finite unitary group whose commutant
is exactly the commutant of the matrix-unit system. Its uniform average
preserves the original scalar derivation bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The signed permutations of a given concrete matrix-unit system. -/
def matrixUnitSignedRepresentation (E : Generator.MatrixUnitSystem ι A) :
    SignedPermutation ι →* unitary A where
  toFun g := ⟨E.hom (signedPermutationHom g : Matrix ι ι ℂ),
    Unitary.map_mem E.hom (signedPermutationHom g).property⟩
  map_one' := by
    apply Subtype.ext
    change E.hom (signedPermutationHom (1 : SignedPermutation ι) : Matrix ι ι ℂ) = 1
    rw [map_one]
    exact map_one E.hom
  map_mul' g k := by
    apply Subtype.ext
    change E.hom (signedPermutationHom (g * k) : Matrix ι ι ℂ) =
      E.hom (signedPermutationHom g : Matrix ι ι ℂ) * E.hom (signedPermutationHom k : Matrix ι ι ℂ)
    rw [map_mul]
    exact map_mul E.hom _ _

theorem matrixUnitSignedRepresentation_mem (E : Generator.MatrixUnitSystem ι A)
    (g : SignedPermutation ι) : (matrixUnitSignedRepresentation E g : A) ∈ E.algebra :=
  ⟨(signedPermutationHom g : Matrix ι ι ℂ), rfl⟩

theorem matrixUnitSignedRepresentation_inl (E : Generator.MatrixUnitSystem ι A)
    (d : ι → ℤˣ) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inl d) : A) = E.hom (signDiagonal d) := by
  change E.hom (signedPermutationHom (SemidirectProduct.inl d) : Matrix ι ι ℂ) = _
  congr 1
  simp [signedPermutationHom, signDiagonalHom, signDiagonalUnitary]

theorem matrixUnitSignedRepresentation_inr (E : Generator.MatrixUnitSystem ι A)
    (σ : Equiv.Perm ι) :
    (matrixUnitSignedRepresentation E (SemidirectProduct.inr σ) : A) =
      E.hom (Matrix.permMatrixHom (R := ℂ) σ) := by
  change E.hom (signedPermutationHom (SemidirectProduct.inr σ) : Matrix ι ι ℂ) = _
  congr 1
  simp [signedPermutationHom, permutationHom, permutationUnitary]

omit [Fintype ι] in
/-- Changing one diagonal sign isolates the corresponding diagonal matrix unit. -/
theorem signDiagonal_reflection (i : ι) :
    signDiagonal (Function.update (1 : ι → ℤˣ) i (-1)) =
      1 - (2 : ℂ) • Matrix.single i i 1 := by
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hji : j = i
    · subst j
      norm_num [signDiagonal, Matrix.diagonal, Matrix.single]
    · simp [signDiagonal, Matrix.diagonal, Matrix.single, hji, Ne.symm hji]
  · have hn : ¬ (i = j ∧ i = k) := fun h => hjk (h.1.symm.trans h.2)
    simp [signDiagonal, Matrix.diagonal, Matrix.single, hjk, hn]

theorem matrixUnit_diagonal_sandwich (E : Generator.MatrixUnitSystem ι A)
    (a : Matrix ι ι ℂ) (i j : ι) :
    E.entry i i * E.hom a * E.entry j j = a i j • E.entry i j := by
  simp only [Generator.MatrixUnitSystem.hom_apply, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, E.mul_entry]
  simp [E.mul_entry, smul_ite]

/-- Commuting with the finite signed-permutation group is enough to commute
with the entire full matrix algebra. -/
theorem commute_matrixUnits_of_signed (E : Generator.MatrixUnitSystem ι A) (x : A)
    (hx : ∀ g, Commute (matrixUnitSignedRepresentation E g : A) x) :
    ∀ i j, Commute (E.entry i j) x := by
  have hd (i : ι) : Commute (E.entry i i) x := by
    have hi := hx (SemidirectProduct.inl (Function.update (1 : ι → ℤˣ) i (-1)))
    rw [matrixUnitSignedRepresentation_inl, signDiagonal_reflection, map_sub, map_one,
      map_smul, E.hom_single, one_smul] at hi
    change (1 - (2 : ℂ) • E.entry i i) * x = x * (1 - (2 : ℂ) • E.entry i i) at hi
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm] at hi
    exact (smul_right_injective A (by norm_num : (2 : ℂ) ≠ 0)) (sub_right_inj.mp hi)
  have hp (σ : Equiv.Perm ι) : Commute (E.hom (Matrix.permMatrixHom (R := ℂ) σ)) x := by
    simpa only [matrixUnitSignedRepresentation_inr] using hx (SemidirectProduct.inr σ)
  intro i j
  have h := ((hd i).mul_left (hp (Equiv.swap i j))).mul_left (hd j)
  simpa only [matrixUnit_diagonal_sandwich, permutationMatrix_apply,
    Equiv.swap_apply_right, ↓reduceIte, one_smul] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual finite-matrix average of an arbitrary ambient operator. -/
def matrixUnitAverage (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H))
    (h : H →L[ℂ] H) : H →L[ℂ] H :=
  finiteUnitaryAverage (matrixUnitSignedRepresentation E) h

theorem matrixUnitAverage_commutes (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H))
    (h : H →L[ℂ] H) : ∀ a ∈ E.algebra, Commute a (matrixUnitAverage E h) := by
  apply (E.commute_algebra_iff _).mpr
  exact commute_matrixUnits_of_signed E _ (finiteUnitaryAverage_commutes _ h)

/-- Finite-dimensional averaging improves the commutant without enlarging
either the displacement or the derivation bound. -/
theorem exists_matrixUnitAverage (M : VonNeumannAlgebra H)
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (hE : E.algebra ≤ M.toStarSubalgebra)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    ∃ h0 : H →L[ℂ] H,
      (∀ a ∈ E.algebra, Commute a h0) ∧ ‖h - h0‖ ≤ δ ∧
      (∀ a ∈ M, ‖h0 * a - a * h0‖ ≤ δ * ‖a‖) ∧
      (IsSelfAdjoint h → IsSelfAdjoint h0) := by
  have hm (g : SignedPermutation ι) : (matrixUnitSignedRepresentation E g : H →L[ℂ] H) ∈ M :=
    hE (matrixUnitSignedRepresentation_mem E g)
  refine ⟨matrixUnitAverage E h, matrixUnitAverage_commutes E h, ?_, ?_, ?_⟩
  · apply norm_sub_finiteUnitaryAverage_le
    intro g
    refine (hb _ (hm g)).trans ?_
    have hn : ‖(matrixUnitSignedRepresentation E g : H →L[ℂ] H)‖ ≤ 1 := by
      calc
        _ = ‖(matrixUnitSignedRepresentation E g : H →L[ℂ] H) * 1‖ := by rw [mul_one]
        _ = ‖(1 : H →L[ℂ] H)‖ := CStarRing.norm_coe_unitary_mul _ _
        _ ≤ 1 := ContinuousLinearMap.norm_id_le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hδ
  · exact finiteUnitaryAverage_derivation_le M _ hm h hb
  · exact finiteUnitaryAverage_selfAdjoint _

end

end KadisonKastler

end OAI
