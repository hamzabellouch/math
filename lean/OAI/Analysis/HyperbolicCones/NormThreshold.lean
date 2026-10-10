import OAI.Analysis.HyperbolicCones.InverseOrder

namespace OAI

/-! The exact scalar threshold of a positive semidefinite matrix. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

theorem posSemidef_scalar_sub_iff {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian) (r : ℝ) :
    (r • (1 : Mat n ℝ) - A).PosSemidef ↔ ∀ x ∈ spectrum ℝ A, x ≤ r := by
  let H : Sym n := ⟨A, hA⟩
  have hshift : cfc (fun x : ℝ => r - x) A = r • (1 : Mat n ℝ) - A := by
    simpa only [neg_one_mul, neg_one_smul, sub_eq_add_neg] using matrix_cfc_affine H r (-1)
  rw [← Matrix.nonneg_iff_posSemidef, ← hshift]
  have h := cfc_nonneg_iff (fun x : ℝ => r - x) A
    (A.finite_real_spectrum.continuousOn _) hA
  simpa only [sub_nonneg] using h

theorem posSemidef_norm_threshold {n : ℕ} [NeZero n] (A : Mat n ℝ)
    (hA : A.PosSemidef) (r : ℝ) :
    (r • (1 : Mat n ℝ) - A).PosSemidef ↔ ‖A‖ ≤ r := by
  rw [posSemidef_scalar_sub_iff A hA.isHermitian r]
  have hgreat := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (p := IsSelfAdjoint) A hA.isHermitian
  constructor
  · intro h
    obtain ⟨x, hx, hnorm⟩ := hgreat.1
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    calc
      ‖A‖ = x := by simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hnorm.symm
      _ ≤ r := h x hx
  · intro h x hx
    exact (le_abs_self x).trans ((hgreat.2 ⟨x, hx, rfl⟩).trans h)

theorem posSemidef_gram_threshold {m n : ℕ} [NeZero n]
    (C : Matrix (Fin m) (Fin n) ℝ) (r : ℝ) :
    (r • (1 : Mat n ℝ) - Cᵀ * C).PosSemidef ↔ ‖C‖ ^ 2 ≤ r := by
  have hp : (Cᵀ * C).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self C
  rw [posSemidef_norm_threshold _ hp]
  have hn : ‖Cᵀ * C‖ = ‖C‖ ^ 2 := by
    simpa only [conjTranspose_eq_transpose_of_trivial, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self C
  rw [hn]

end Paper256

end

end OAI
