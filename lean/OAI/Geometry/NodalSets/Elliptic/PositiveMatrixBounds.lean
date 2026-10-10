import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma real_dot_self_nonneg (v : n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (v i))

lemma positive_matrix_inverse_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v))
    (v : n → ℝ) :
    b⁻¹ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A⁻¹ *ᵥ v) ∧
    v ⬝ᵥ (A⁻¹ *ᵥ v) ≤ a⁻¹ * (v ⬝ᵥ v) := by
  let u := A⁻¹ *ᵥ v
  have hu : A *ᵥ u = v := by
    dsimp [u]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  have hs : Aᵀ = A := by simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
  have hcross' : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, hu, dotProduct_comm]
  have hpos := hA.posSemidef.dotProduct_mulVec_nonneg (v - b • u)
  simp only [star_trivial, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hcross', hu] at hpos
  have hnorm := real_dot_self_nonneg (v - a • u)
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, dotProduct_comm u v] at hnorm
  have hu_lo := hlo u
  rw [hu, dotProduct_comm u v] at hu_lo
  have hupper : a * (v ⬝ᵥ u) ≤ v ⬝ᵥ v := by
    nlinarith [mul_le_mul_of_nonneg_left hu_lo ha.le]
  have hlower : v ⬝ᵥ v ≤ b * (v ⬝ᵥ u) := by
    have h := hhi v
    rw [dotProduct_comm u v] at hpos
    nlinarith
  constructor
  · change b⁻¹ * (v ⬝ᵥ v) ≤ v ⬝ᵥ u
    rw [inv_mul_eq_div, div_le_iff₀ hb]
    nlinarith
  · change v ⬝ᵥ u ≤ a⁻¹ * (v ⬝ᵥ v)
    rw [inv_mul_eq_div, le_div_iff₀ ha]
    nlinarith

lemma positive_matrix_eigenvalue_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b : ℝ)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) (i : n) :
    a ≤ hA.1.eigenvalues i ∧ hA.1.eigenvalues i ≤ b := by
  have he : (⇑(hA.1.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.1.eigenvectorBasis i)) = 1 := by
    have hh := real_inner_self_eq_norm_sq (hA.1.eigenvectorBasis i)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      hA.1.eigenvectorBasis.orthonormal.1 i, one_pow] using hh
  have hl := hlo ⇑(hA.1.eigenvectorBasis i)
  have hh := hhi ⇑(hA.1.eigenvectorBasis i)
  rw [hA.1.mulVec_eigenvectorBasis, dotProduct_smul, he] at hl hh
  simpa using And.intro hl hh

lemma positive_matrix_determinant_bounds (A : Matrix n n ℝ) (hA : A.PosDef)
    (a b : ℝ) (ha : 0 ≤ a)
    (hlo : ∀ v : n → ℝ, a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hhi : ∀ v : n → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v)) :
    a ^ Fintype.card n ≤ A.det ∧ A.det ≤ b ^ Fintype.card n := by
  rw [hA.1.det_eq_prod_eigenvalues]
  constructor
  · simpa using Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : n ↦ a)
      (g := hA.1.eigenvalues) (fun _ _ ↦ ha)
      (fun i _ ↦ (positive_matrix_eigenvalue_bounds A hA a b hlo hhi i).1)
  · simpa using Finset.prod_le_prod₀ (s := Finset.univ) (f := hA.1.eigenvalues)
      (g := fun _ : n ↦ b) (fun i _ ↦ (hA.eigenvalues_pos i).le)
      (fun i _ ↦ (positive_matrix_eigenvalue_bounds A hA a b hlo hhi i).2)

end
end Yau.Geometry

end OAI
