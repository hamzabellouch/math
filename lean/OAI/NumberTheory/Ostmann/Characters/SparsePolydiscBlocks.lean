import OAI.NumberTheory.Ostmann.Characters.SparsePolydiscScalar

namespace OAI

/-! # Uniform side and lower bounds on the complex parameter polydisc -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def polydiscSparseScalar {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (c d : ℂ) : ℂ :=
  1 + c * residueKernelScalar S (localSparseKernel E) +
    d * residueKernelScalar S (localSparseSquare E)

noncomputable def polydiscSparseSide {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) (x : ZMod p) : ℂ :=
  c * residueKernelSide S T (localSparseKernel E) x +
    d * residueKernelSide S T (localSparseSquare E) x

noncomputable def polydiscSparseLower {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (c d : ℂ) (f : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  c * residueKernelLower S T (localSparseKernel E) f x +
    d * residueKernelLower S T (localSparseSquare E) f x

theorem polydiscSparseSide_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (ε : ℝ) (hε : 0 ≤ ε) (hE : (E.card : ℝ) ≤ ε * p)
    (c d : ℂ) (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000)
    (hproj : residueVectorNorm (centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector T))) ≤ 2 * ε / Real.sqrt (p : ℝ))
    (hu : residueVectorNorm (uniformResidueVector T) ≤ 2 / Real.sqrt (p : ℝ)) :
    residueVectorNorm (polydiscSparseSide S T E c d) ≤ 6 * ε / Real.sqrt (p : ℝ) := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul, residueVectorNorm_smul]
  let q := ε / Real.sqrt (p : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h1 : residueVectorNorm (residueKernelSide S T (localSparseKernel E)) ≤ (17 / 10) * q := by
    rw [localSparseKernel, residueKernelSide_sparse_norm]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 17 / 20)]
    apply (mul_le_mul_of_nonneg_left hproj (by norm_num : (0 : ℝ) ≤ 17 / 20)).trans_eq
    dsimp [q]
    ring
  have h2 : residueVectorNorm (residueKernelSide S T (localSparseSquare E)) ≤ (289 / 200) * q := by
    apply (residueKernelSide_square_norm_le S T E (17 / 20) ε hε hE).trans
    apply (mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ (17 / 20) ^ 2 * ε)).trans_eq
    dsimp [q]
    ring
  have hh := add_le_add (mul_le_mul hc h1 (residueVectorNorm_nonneg _) (by norm_num))
    (mul_le_mul hd h2 (residueVectorNorm_nonneg _) (by norm_num))
  have hlast : (103 / 50) * ((17 / 10) * q) +
      (10609 / 10000) * ((289 / 200) * q) ≤ 6 * ε / Real.sqrt (p : ℝ) := by
    have he : 6 * ε / Real.sqrt (p : ℝ) = 6 * q := by dsimp [q]; ring
    rw [he]
    nlinarith only [hq]
  exact hh.trans hlast

theorem polydiscSparseLower_norm_le {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000) (hE : (E.card : ℝ) ≤ ε * p)
    (c d : ℂ) (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000)
    (f : ZMod p → ℂ) :
    residueVectorNorm (polydiscSparseLower S T E c d f) ≤ (9 / 10 : ℝ) * residueVectorNorm f := by
  apply (residueVectorNorm_add_le _ _).trans
  rw [residueVectorNorm_smul, residueVectorNorm_smul]
  have h1 := residueVectorNorm_cross_kernel_le S T E hST (17 / 20) (by norm_num) f
  have h2 := residueVectorNorm_square_kernel_le S T E (17 / 20) ε hε hE f
  have hh := add_le_add (mul_le_mul hc h1 (residueVectorNorm_nonneg _) (by norm_num))
    (mul_le_mul hd h2 (residueVectorNorm_nonneg _) (by norm_num))
  have hcoef : (103 / 50) * ((17 / 20) / 2) +
      (10609 / 10000) * ((17 / 20) ^ 2 * ε) ≤ (9 / 10 : ℝ) := by linarith
  apply hh.trans
  have he : (103 / 50) * ((17 / 20 / 2) * residueVectorNorm f) +
      (10609 / 10000) * ((17 / 20) ^ 2 * ε * residueVectorNorm f) =
      ((103 / 50) * ((17 / 20) / 2) + (10609 / 10000) * ((17 / 20) ^ 2 * ε)) *
        residueVectorNorm f := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hcoef (residueVectorNorm_nonneg f)

end Ostmann

end OAI
