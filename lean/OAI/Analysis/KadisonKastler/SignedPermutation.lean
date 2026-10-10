import OAI.Analysis.FactorGeneration.MatrixUnits
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace OAI

/-! # A finite unitary group spanning a full matrix algebra -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Permutations act on diagonal signs by permuting their coordinates. -/
def permuteSigns : Equiv.Perm ι →* MulAut (ι → ℤˣ) where
  toFun σ := {
    toFun := fun d i => d (σ⁻¹ i)
    invFun := fun d i => d (σ i)
    left_inv := by intro d; funext i; simp
    right_inv := by intro d; funext i; simp
    map_mul' := by intros; rfl }
  map_one' := by ext d i; rfl
  map_mul' σ τ := by ext d i; rfl

abbrev SignedPermutation (ι : Type*) := (ι → ℤˣ) ⋊[permuteSigns] Equiv.Perm ι

instance : Fintype (SignedPermutation ι) :=
  Fintype.ofEquiv ((ι → ℤˣ) × Equiv.Perm ι) SemidirectProduct.equivProd.symm

def signDiagonal (d : ι → ℤˣ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ((d i : ℤ) : ℂ))

omit [Fintype ι] in
theorem signDiagonal_star (d : ι → ℤˣ) : star (signDiagonal d) = signDiagonal d := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [signDiagonal, Matrix.star_apply]
  · simp [signDiagonal, Matrix.star_apply, Matrix.diagonal, hij, Ne.symm hij]

theorem signDiagonal_mul (d e : ι → ℤˣ) :
    signDiagonal (d * e) = signDiagonal d * signDiagonal e := by
  simp [signDiagonal, Matrix.diagonal_mul_diagonal]

theorem signDiagonal_sq (d : ι → ℤˣ) : signDiagonal d * signDiagonal d = 1 := by
  rw [← signDiagonal_mul]
  have hd : d * d = 1 := by funext i; exact Int.units_mul_self (d i)
  rw [hd]
  simp [signDiagonal]

def signDiagonalUnitary (d : ι → ℤˣ) : unitary (Matrix ι ι ℂ) :=
  ⟨signDiagonal d, by
    change star (signDiagonal d) * signDiagonal d = 1 ∧ signDiagonal d * star (signDiagonal d) = 1
    rw [signDiagonal_star]
    exact ⟨signDiagonal_sq d, signDiagonal_sq d⟩⟩

def signDiagonalHom : (ι → ℤˣ) →* unitary (Matrix ι ι ℂ) where
  toFun := signDiagonalUnitary
  map_one' := by apply Subtype.ext; simp [signDiagonalUnitary, signDiagonal]
  map_mul' d e := Subtype.ext (signDiagonal_mul d e)

def permutationUnitary (σ : Equiv.Perm ι) : unitary (Matrix ι ι ℂ) :=
  ⟨Matrix.permMatrixHom (R := ℂ) σ, by
    change star (Matrix.permMatrixHom (R := ℂ) σ) * Matrix.permMatrixHom (R := ℂ) σ = 1 ∧
      Matrix.permMatrixHom (R := ℂ) σ * star (Matrix.permMatrixHom (R := ℂ) σ) = 1
    have hs : star (Matrix.permMatrixHom (R := ℂ) σ) = Matrix.permMatrixHom (R := ℂ) σ⁻¹ := by
      change star (σ⁻¹.permMatrix ℂ) = (σ⁻¹)⁻¹.permMatrix ℂ
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
    rw [hs, ← map_mul, ← map_mul]
    simp⟩

def permutationHom : Equiv.Perm ι →* unitary (Matrix ι ι ℂ) where
  toFun := permutationUnitary
  map_one' := Subtype.ext (map_one (Matrix.permMatrixHom (R := ℂ)))
  map_mul' σ τ := Subtype.ext (map_mul (Matrix.permMatrixHom (R := ℂ)) σ τ)

theorem permutationMatrix_apply (σ : Equiv.Perm ι) (i j : ι) :
    Matrix.permMatrixHom (R := ℂ) σ i j = if i = σ j then 1 else 0 := by
  change (if j ∈ (some (σ⁻¹ i) : Option ι) then (1 : ℂ) else 0) = _
  simp [Equiv.eq_symm_apply, eq_comm]


theorem permutation_signDiagonal (σ : Equiv.Perm ι) (d : ι → ℤˣ) :
    Matrix.permMatrixHom (R := ℂ) σ * signDiagonal d =
      signDiagonal (permuteSigns σ d) * Matrix.permMatrixHom (R := ℂ) σ := by
  ext i j
  simp only [signDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, permutationMatrix_apply]
  by_cases hij : i = σ j
  · subst i
    simp [permuteSigns]
  · simp [hij]

/-- The finite signed-permutation group acts by actual unitary matrices. -/
def signedPermutationHom : SignedPermutation ι →* unitary (Matrix ι ι ℂ) :=
  SemidirectProduct.lift signDiagonalHom permutationHom (fun σ => by
    apply MonoidHom.ext
    intro d
    apply Subtype.ext
    change signDiagonal (permuteSigns σ d) =
      Matrix.permMatrixHom (R := ℂ) σ * signDiagonal d * (↑((permutationHom σ)⁻¹) : Matrix ι ι ℂ)
    rw [permutation_signDiagonal, mul_assoc]
    have hi : Matrix.permMatrixHom (R := ℂ) σ * (↑((permutationHom σ)⁻¹) : Matrix ι ι ℂ) = 1 :=
      congrArg (fun u : unitary (Matrix ι ι ℂ) => u.val) (mul_inv_cancel (permutationHom σ))
    rw [hi, mul_one])

end

end KadisonKastler

end OAI
