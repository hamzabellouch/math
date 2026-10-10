import OAI.Analysis.HyperbolicCones.CompressionBasic

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

def conjugatePencil {n : ℕ} (L : V →ₗ[ℝ] Sym n) (U : Mat n ℝ) : V →ₗ[ℝ] Sym n where
  toFun x := ⟨Uᴴ * (L x : Mat n ℝ) * U,
    Matrix.isHermitian_conjTranspose_mul_mul U (L x).property⟩
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c x := by
    apply Subtype.ext
    simp

def restrictPencil {m n : ℕ} (L : V →ₗ[ℝ] Sym n) (f : Fin m → Fin n) :
    V →ₗ[ℝ] Sym m where
  toFun x := ⟨(L x : Mat n ℝ).submatrix f f, (sym_isHermitian (L x)).submatrix f⟩
  map_add' x y := by apply Subtype.ext; ext i j; simp
  map_smul' c x := by apply Subtype.ext; ext i j; simp

theorem conjugatePencil_posSemidef_iff {n : ℕ} (L : V →ₗ[ℝ] Sym n)
    (U : Mat n ℝ) (hU : IsUnit U) (x : V) :
    (conjugatePencil L U x : Mat n ℝ).PosSemidef ↔ (L x : Mat n ℝ).PosSemidef := by
  change (Uᴴ * (L x : Mat n ℝ) * U).PosSemidef ↔ _
  simpa only [Matrix.star_eq_conjTranspose] using hU.posSemidef_star_left_conjugate_iff

theorem spectral_conjugate_diagonal {n : ℕ} (A : Sym n) :
    ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)ᴴ * (A : Mat n ℝ) *
      ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ) = Matrix.diagonal (sym_isHermitian A).eigenvalues := by
  simpa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def] using (sym_isHermitian A).conjStarAlgAut_star_eigenvectorUnitary

theorem spectral_conjugate_zero_column {n : ℕ} (A B : Sym n)
    (hA : (A : Mat n ℝ).PosSemidef)
    (hker : ∀ v : Fin n → ℝ, (A : Mat n ℝ) *ᵥ v = 0 → (B : Mat n ℝ) *ᵥ v = 0)
    (i : Fin n) (hi : ¬ 0 < (sym_isHermitian A).eigenvalues i) (j : Fin n) :
    (((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)ᴴ * (B : Mat n ℝ) *
      ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)) j i = 0 := by
  let U : Mat n ℝ := (sym_isHermitian A).eigenvectorUnitary
  have heig : (sym_isHermitian A).eigenvalues i = 0 :=
    le_antisymm (le_of_not_gt hi) (hA.eigenvalues_nonneg i)
  have ha : (A : Mat n ℝ) *ᵥ (U *ᵥ Pi.single i 1) = 0 := by
    rw [show U *ᵥ Pi.single i 1 = ⇑((sym_isHermitian A).eigenvectorBasis i) from
      (sym_isHermitian A).eigenvectorUnitary_mulVec i]
    rw [(sym_isHermitian A).mulVec_eigenvectorBasis, heig, zero_smul]
  have hb := hker (U *ᵥ Pi.single i 1) ha
  have hz : (Uᴴ * (B : Mat n ℝ) * U) *ᵥ Pi.single i 1 = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hb, mulVec_zero]
  have hv := congrFun hz j
  simpa using hv

theorem spectral_conjugate_zero_row {n : ℕ} (A B : Sym n)
    (hA : (A : Mat n ℝ).PosSemidef)
    (hker : ∀ v : Fin n → ℝ, (A : Mat n ℝ) *ᵥ v = 0 → (B : Mat n ℝ) *ᵥ v = 0)
    (i : Fin n) (hi : ¬ 0 < (sym_isHermitian A).eigenvalues i) (j : Fin n) :
    (((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)ᴴ * (B : Mat n ℝ) *
      ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ)) i j = 0 := by
  have hh := Matrix.isHermitian_conjTranspose_mul_mul
    ((sym_isHermitian A).eigenvectorUnitary : Mat n ℝ) B.property
  have hs := hh.apply j i
  have hz := spectral_conjugate_zero_column A B hA hker i hi j
  simpa using hs.trans hz

end Paper256

end

end OAI
