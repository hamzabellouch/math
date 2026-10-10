import OAI.Analysis.KadisonKastler.MatrixUltrapower

namespace OAI

/-! # The commutant of the scalar matrix copy

Commuting with all scalar matrix units forces a matrix over any complex
C⋆-algebra to be a constant diagonal matrix. The corresponding statement
for unitaries retains an actual unitary coefficient.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The constant diagonal copy of the coefficient algebra. -/
def matrixScalarHom : A →⋆ₐ[ℂ] CStarMatrix ι ι A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    { (Matrix.scalarAlgHom ι ℂ : A →ₐ[ℂ] Matrix ι ι A) with
      map_star' := by
        intro a
        ext i j
        change (if i = j then star a else 0) = star (if j = i then a else 0)
        by_cases hij : i = j <;> simp [hij, eq_comm] }

@[simp]
theorem matrixScalarHom_apply (a : A) (i j : ι) :
    matrixScalarHom a i j = if i = j then a else 0 := rfl

theorem matrixScalarHom_injective [Nonempty ι] :
    Function.Injective (matrixScalarHom : A →⋆ₐ[ℂ] CStarMatrix ι ι A) := by
  intro a b h
  let i : ι := Classical.arbitrary ι
  simpa only [matrixScalarHom_apply, ite_true] using
    congrArg (fun x : CStarMatrix ι ι A => x i i) h

local instance commutantScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance commutantScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

/-- The scalar matrix units, viewed in a matrix algebra over `A`. -/
theorem coefficientMatrixMap_scalar_single (i j : ι) :
    coefficientMatrixMap (StarAlgHom.ofId ℂ A)
      (CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ))) =
        CStarMatrix.ofMatrix (Matrix.single i j (1 : A)) := by
  apply CStarMatrix.ext
  intro k l
  simp [coefficientMatrixMap_apply, Matrix.single_apply]

/-- Every constant diagonal matrix commutes with the scalar matrix copy. -/
theorem matrixScalarHom_commutes_scalar (a : A) (s : CStarMatrix ι ι ℂ) :
    coefficientMatrixMap (StarAlgHom.ofId ℂ A) s * matrixScalarHom a =
      matrixScalarHom a * coefficientMatrixMap (StarAlgHom.ofId ℂ A) s := by
  apply CStarMatrix.ext
  intro i j
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    coefficientMatrixMap_apply]
  exact Algebra.commutes (s i j) a

/-- It is enough to commute with the scalar matrix copy to be constant diagonal. -/
theorem exists_matrixScalarHom_of_commutes (x : CStarMatrix ι ι A)
    (hx : ∀ s : CStarMatrix ι ι ℂ,
      coefficientMatrixMap (StarAlgHom.ofId ℂ A) s * x =
        x * coefficientMatrixMap (StarAlgHom.ofId ℂ A) s) :
    ∃ a : A, x = matrixScalarHom a := by
  have hm : CStarMatrix.ofMatrix.symm x ∈ Set.range (Matrix.scalar ι) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro i j hij
    have h := hx (CStarMatrix.ofMatrix (Matrix.single i j (1 : ℂ)))
    rw [coefficientMatrixMap_scalar_single] at h
    exact h
  obtain ⟨a, ha⟩ := hm
  exact ⟨a, congrArg CStarMatrix.ofMatrix ha.symm⟩

/-- A unitary in the scalar-matrix commutant has a unitary coefficient. -/
theorem exists_unitary_matrixScalarHom_of_commutes [Nonempty ι]
    (u : unitary (CStarMatrix ι ι A))
    (hu : ∀ s : CStarMatrix ι ι ℂ,
      coefficientMatrixMap (StarAlgHom.ofId ℂ A) s * (u : CStarMatrix ι ι A) =
        (u : CStarMatrix ι ι A) * coefficientMatrixMap (StarAlgHom.ofId ℂ A) s) :
    ∃ v : unitary A, (u : CStarMatrix ι ι A) = matrixScalarHom (v : A) := by
  obtain ⟨a, ha⟩ := exists_matrixScalarHom_of_commutes (u : CStarMatrix ι ι A) hu
  have h₁ : star a * a = 1 := by
    apply matrixScalarHom_injective (ι := ι)
    simpa only [map_mul, StarHomClass.map_star, map_one, ← ha] using u.property.1
  have h₂ : a * star a = 1 := by
    apply matrixScalarHom_injective (ι := ι)
    simpa only [map_mul, StarHomClass.map_star, map_one, ← ha] using u.property.2
  exact ⟨⟨a, h₁, h₂⟩, ha⟩

end

end KadisonKastler

end OAI
