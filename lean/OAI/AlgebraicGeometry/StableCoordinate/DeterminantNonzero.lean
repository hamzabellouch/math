import OAI.AlgebraicGeometry.StableCoordinate.DeterminantGradings

namespace OAI

/-!
# Concrete nonvanishing certificates in the determinant quotient

These elementary evaluations verify the nonzero factors used to split the
highest auxiliary part of `v`, without assuming the unproved headline.
-/

noncomputable section

namespace StableCoordinate.Obstruction

open MvPolynomial

variable (k : Type*) [CommRing k]

/-- Evaluate the determinant quotient at any point satisfying its defining relation. -/
def determinantEval (point : Fin 5 → k)
    (hp : point 0 * point 3 - point 2 * point 1 - 1 = 0) : C k →ₐ[k] k :=
  Ideal.Quotient.liftₐ (idealC k) (MvPolynomial.aeval point) (by
    intro p hp'
    have hker : idealC k ≤ RingHom.ker (MvPolynomial.aeval point) := by
      apply Ideal.span_le.mpr
      intro q hq
      rcases Set.mem_singleton_iff.mp hq with rfl
      exact RingHom.mem_ker.mpr (by simpa [determinantRelation] using hp)
    exact hker hp')

@[simp]
theorem determinantEval_cX (point : Fin 5 → k)
    (hp : point 0 * point 3 - point 2 * point 1 - 1 = 0) (i : Fin 5) :
    determinantEval k point hp (cX k i) = point i := by
  change (aeval point) (X i) = point i
  simp

/-- A specific point where the top auxiliary part and both of its factors are one. -/
def highTestPoint : Fin 5 → k := ![1, 0, 0, 1, 1]

/-- The test point does lie on the determinant hypersurface. -/
theorem highTestPoint_relation :
    highTestPoint k 0 * highTestPoint k 3 - highTestPoint k 2 * highTestPoint k 1 - 1 = 0 := by
  simp [highTestPoint]

/-- The associated evaluation is an actual algebra homomorphism. -/
def highTestEval : C k →ₐ[k] k := determinantEval k (highTestPoint k) (highTestPoint_relation k)

@[simp] theorem highTestEval_cX (i : Fin 5) : highTestEval k (cX k i) = highTestPoint k i :=
  determinantEval_cX k _ _ i

@[simp] theorem highTestEval_vHigh : highTestEval k (vHigh k) = 1 := by
  simp [vHigh, highTestPoint]

@[simp] theorem highTestEval_au_sub_d :
    highTestEval k (cX k 0 * cX k 4 - cX k 1) = 1 := by
  simp [highTestPoint]

@[simp] theorem highTestEval_au_add_d :
    highTestEval k (cX k 0 * cX k 4 + cX k 1) = 1 := by
  simp [highTestPoint]

/-- The finite list of displayed generators really generates the actual quotient algebra. -/
theorem adjoin_range_cX : Algebra.adjoin k (Set.range (cX k)) = ⊤ := by
  have heval : MvPolynomial.aeval (cX k) = Ideal.Quotient.mkₐ k (idealC k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [cX]
  rw [Algebra.adjoin_range_eq_range_aeval, heval]
  exact (AlgHom.range_eq_top _).mpr Ideal.Quotient.mk_surjective

variable [Nontrivial k]

/-- The source's highest auxiliary part is genuinely nonzero. -/
theorem vHigh_ne_zero : vHigh k ≠ 0 := by
  intro h
  have hh := congrArg (highTestEval k) h
  simp at hh

/-- Both difference-of-squares factors are nonzero in the actual quotient. -/
theorem au_sub_d_ne_zero : cX k 0 * cX k 4 - cX k 1 ≠ 0 := by
  intro h
  have hh := congrArg (highTestEval k) h
  simp at hh

theorem au_add_d_ne_zero : cX k 0 * cX k 4 + cX k 1 ≠ 0 := by
  intro h
  have hh := congrArg (highTestEval k) h
  simp at hh

theorem cX_a_ne_zero : cX k 0 ≠ 0 := by
  intro h
  have hh := congrArg (highTestEval k) h
  simp [highTestPoint] at hh

theorem cX_u_ne_zero : cX k 4 ≠ 0 := by
  intro h
  have hh := congrArg (highTestEval k) h
  simp [highTestPoint] at hh

/-- The lower auxiliary term is also genuinely nonzero. -/
theorem vLow_ne_zero : vLow k ≠ 0 := by
  let e : C k →ₐ[k] k := determinantEval k ![1, 0, 1, 1, 0] (by simp)
  have he : e (vLow k) = 1 := by
    simp [e, vLow]
  intro h
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- The second weight-one coordinate is nonzero as well. -/
theorem cX_d_ne_zero : cX k 1 ≠ 0 := by
  let e : C k →ₐ[k] k := determinantEval k ![1, 1, 0, 1, 0] (by simp)
  have he : e (cX k 1) = 1 := by simp [e]
  intro h
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- Thus the auxiliary degree-two projection of `v` is nonzero. -/
theorem auxiliary_proj_v_two_ne_zero : GradedAlgebra.proj (auxiliaryPiece k) 2 (v k) ≠ 0 := by
  rw [auxiliary_proj_v_two]
  exact vHigh_ne_zero k

end StableCoordinate.Obstruction

end

end OAI
