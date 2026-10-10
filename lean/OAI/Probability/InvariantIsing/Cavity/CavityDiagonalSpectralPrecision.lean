import OAI.Probability.InvariantIsing.Cavity.CavitySpectralTransform
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralGap
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRecursion

namespace OAI

/-! The precision assumptions in the rooted Gaussian calculation follow
from the actual upper spectral gap when the base matrix is diagonal. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma finiteInverse_antitone_pos {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    finiteInverse ρ eig hρ hsum x ≤ finiteInverse ρ eig hρ hsum y := by
  have hx := hy.trans_le hyx
  by_contra! h
  have hh := finiteResolvent_strictAnti (fun a => (hρ a).le) hsum
    (finiteInverse_spec ρ eig hρ hsum hy).1 h
  rw [(finiteInverse_spec ρ eig hρ hsum hx).2,
    (finiteInverse_spec ρ eig hρ hsum hy).2] at hh
  exact (not_lt_of_ge hyx) hh

lemma cavitySpectralMatrixPath_diagonal_pos {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (e : Fin d → ℝ) (he : (Matrix.diagonal e).IsHermitian)
    (a : ι) (heig : ∀ i, he.eigenvalues i ≤ eig a) (hemax : ∀ i, e i ≤ eig a) {x : ℝ} (hx : 0 < x) :
    cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x =
      Matrix.diagonal (fun i => (finiteInverse ρ eig hρ hsum x - e i)⁻¹) := by
  rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum _ he a heig hx]
  have hshift : finiteInverse ρ eig hρ hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal e = Matrix.diagonal (fun i => finiteInverse ρ eig hρ hsum x - e i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [hshift, Matrix.diagonal_mul_diagonal]
  have hg i : finiteInverse ρ eig hρ hsum x - e i ≠ 0 :=
    (sub_pos.mpr ((hemax i).trans_lt ((finiteInverse_spec ρ eig hρ hsum hx).1 a))).ne'
  simp [hg]

theorem cavity_diagonal_spectral_step_precision {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (e : Fin d → ℝ)
    (he : (Matrix.diagonal e).IsHermitian)
    (a : ι) (heig : ∀ i, he.eigenvalues i ≤ eig a) (hemax : ∀ i, e i ≤ eig a)
    (hK : (A - Matrix.diagonal e).transpose = A - Matrix.diagonal e)
    (hA : (eig a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x y ζ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hζ : 0 ≤ ζ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hΔ : cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x -
      cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he y = ζ • S) :
    (cavityFactorPrecision (ζ • cavityBackwardQuadratic (A - Matrix.diagonal e)
      (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he y))
        (CFC.sqrt S)).PosDef := by
  have hx := hy.trans_le hyx
  let b₀ := finiteInverse ρ eig hρ hsum x
  let b₁ := finiteInverse ρ eig hρ hsum y
  have hb₀ : eig a < b₀ := (finiteInverse_spec ρ eig hρ hsum hx).1 a
  have hb₁ : b₀ ≤ b₁ := finiteInverse_antitone_pos ρ eig hρ hsum hy hyx
  rw [cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hy]
  apply cavity_scaled_step_precision (A - Matrix.diagonal e) S hK hS ζ hζ
    (fun i => (b₀ - e i)⁻¹) (fun i => (b₁ - e i)⁻¹)
  · intro i
    exact inv_pos.mpr (sub_pos.mpr ((hemax i).trans_lt hb₀))
  · intro i
    exact (inv_pos.mpr (sub_pos.mpr ((hemax i).trans_lt (hb₀.trans_le hb₁)))).le
  · intro i
    exact inv_anti₀ (sub_pos.mpr ((hemax i).trans_lt hb₀)) (sub_le_sub_right hb₁ (e i))
  · right
    intro i
    exact inv_pos.mpr (sub_pos.mpr ((hemax i).trans_lt (hb₀.trans_le hb₁)))
  · exact cavity_resolvent_diagonal_gap A e (eig a) b₀ hA hb₀
  · simpa only [cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hx,
      cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hy] using hΔ

theorem cavity_diagonal_spectral_terminal_precision {ι : Type*} [Fintype ι] {d : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A : Matrix (Fin d) (Fin d) ℝ) (e : Fin d → ℝ)
    (he : (Matrix.diagonal e).IsHermitian)
    (a : ι) (heig : ∀ i, he.eigenvalues i ≤ eig a) (hemax : ∀ i, e i ≤ eig a)
    (hK : (A - Matrix.diagonal e).transpose = A - Matrix.diagonal e)
    (hA : (eig a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (cavityFactorPrecision (A - Matrix.diagonal e)
      (CFC.sqrt (cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x))).PosDef := by
  let H := cavitySpectralMatrixPath ρ eig hρ hsum (Matrix.diagonal e) he x
  have hdiag := cavitySpectralMatrixPath_diagonal_pos ρ eig hρ hsum e he a heig hemax hx
  have hH : H.PosSemidef := by
    rw [show H = _ from hdiag]
    exact Matrix.PosSemidef.diagonal (fun i => (inv_pos.mpr
      (sub_pos.mpr ((hemax i).trans_lt ((finiteInverse_spec ρ eig hρ hsum hx).1 a)))).le)
  apply cavity_resolvent_terminal_precision A (CFC.sqrt H) e (eig a)
    (finiteInverse ρ eig hρ hsum x) hK hA hemax ((finiteInverse_spec ρ eig hρ hsum hx).1 a)
  rw [cavity_covariance_sqrt_factor H hH]
  exact hdiag.symm

end InvariantIsing

end

end OAI
