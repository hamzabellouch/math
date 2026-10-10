import OAI.NumberTheory.Ostmann.Characters.FiniteKernelBlocks

namespace OAI

/-! # The actual local blocks of `(1+b)^2` at the fixed parameter `17/20` -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def localSparseKernel {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) : ZMod p → ℂ := sparseAdditiveKernel E (17 / 20)

noncomputable def localSparseSquare {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (x : ZMod p) : ℂ := localSparseKernel E x * localSparseKernel E x

noncomputable def localSparseScalar {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) : ℂ :=
  1 + 2 * residueKernelScalar S (localSparseKernel E) + residueKernelScalar S (localSparseSquare E)

noncomputable def localSparseSide {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  2 * residueKernelSide S T (localSparseKernel E) x + residueKernelSide S T (localSparseSquare E) x

noncomputable def localSparseLower {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (f : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  2 * residueKernelLower S T (localSparseKernel E) f x +
    residueKernelLower S T (localSparseSquare E) f x

theorem localSparseSide_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p)
    (hproj : residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector T))) ≤ 2 * ε / Real.sqrt (p : ℝ))
    (hu : residueVectorNorm (uniformResidueVector T) ≤ 2 / Real.sqrt (p : ℝ)) :
    residueVectorNorm (localSparseSide S T E) ≤ 6 * ε / Real.sqrt (p : ℝ) := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have h1 := residueKernelSide_sparse_norm S T E (17 / 20)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 17 / 20)] at h1
  have h2 := residueKernelSide_square_norm_le S T E (17 / 20) ε hε hE
  change residueVectorNorm (residueKernelSide S T (localSparseSquare E)) ≤ _ at h2
  have h3 := mul_le_mul_of_nonneg_left hproj (by norm_num : (0 : ℝ) ≤ 17 / 20)
  rw [← h1] at h3
  have h4 := h2.trans (mul_le_mul_of_nonneg_left hu (by positivity))
  have hn : 0 ≤ ε / Real.sqrt (p : ℝ) := by positivity
  dsimp only [localSparseKernel] at *
  calc
    _ ≤ 2 * ((17 / 20) * (2 * ε / Real.sqrt (p : ℝ))) +
        (17 / 20) ^ 2 * ε * (2 / Real.sqrt (p : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left h3 (by norm_num)) h4
    _ = (969 / 200 : ℝ) * (ε / Real.sqrt (p : ℝ)) := by ring
    _ ≤ 6 * (ε / Real.sqrt (p : ℝ)) := mul_le_mul_of_nonneg_right (by norm_num) hn
    _ = _ := by ring

theorem localSparseLower_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000) (hE : (E.card : ℝ) ≤ ε * p)
    (f : ZMod p → ℂ) :
    residueVectorNorm (localSparseLower S T E f) ≤ (9 / 10 : ℝ) * residueVectorNorm f := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have h1 := residueVectorNorm_cross_kernel_le S T E hST (17 / 20) (by norm_num) f
  have h2 := residueVectorNorm_square_kernel_le S T E (17 / 20) ε hε hE f
  change residueVectorNorm (residueKernelLower S T (localSparseKernel E) f) ≤ _ at h1
  change residueVectorNorm (residueKernelLower S T (localSparseSquare E) f) ≤ _ at h2
  have hcoef : (2 : ℝ) * ((17 / 20) / 2) + (17 / 20) ^ 2 * ε ≤ 9 / 10 := by linarith
  have hh := mul_le_mul_of_nonneg_right hcoef (residueVectorNorm_nonneg f)
  nlinarith only [h1, h2, hh]

end Ostmann

end OAI
