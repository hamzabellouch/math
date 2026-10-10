import OAI.InformationTheory.AmplitudeDamping.LogDetConvexity

namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

theorem entropy_nonneg {A : Matrix ι ι ℂ} (hA : IsState A) : 0 ≤ entropy A := by
  rw [entropy_eq_sum hA.1.isHermitian]
  have hs : ∑ i, hA.1.isHermitian.eigenvalues i = 1 := by
    simpa using congrArg Complex.re
      (hA.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hA.2)
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hA.1.eigenvalues_nonneg i)
  rw [← hs]
  exact Finset.single_le_sum (fun j _ ↦ hA.1.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- The square-moduli in each row of a unitary matrix sum to one. -/
theorem unitary_row_sq_sum (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A i i).re) (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

/-- The square-moduli in each column of a unitary matrix sum to one. -/
theorem unitary_col_sq_sum (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ ↦ (A j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_re, Complex.normSq_apply,
    mul_comm] using h

/-- The ordinary diagonal is a doubly stochastic mixing of the spectral diagonal. -/
theorem diag_eq_spectral_mix {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) :
    (A i i).re = ∑ j, Complex.normSq (hA.eigenvectorUnitary i j) * hA.eigenvalues j := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.mul_diagonal, Matrix.star_apply, Complex.mul_re, Complex.mul_im,
    Complex.normSq_apply]
  ring

/-- Pinching in any fixed orthonormal coordinate basis increases entropy. -/
theorem entropy_le_diagonal {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    entropy A ≤ ∑ i, Real.negMulLog (A i i).re := by
  let U := hA.isHermitian.eigenvectorUnitary
  have hi (i : ι) :
      ∑ j, Complex.normSq (U i j) * Real.negMulLog (hA.isHermitian.eigenvalues j) ≤
        Real.negMulLog (A i i).re := by
    rw [diag_eq_spectral_mix hA.isHermitian]
    simpa only [U, smul_eq_mul] using
      Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
        (w := fun j ↦ Complex.normSq (U i j))
        (p := hA.isHermitian.eigenvalues) (fun j _ ↦ Complex.normSq_nonneg _)
        (by simpa using unitary_row_sq_sum U i)
        (fun j _ ↦ hA.eigenvalues_nonneg j)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
  rw [Finset.sum_comm] at h
  simp only [← Finset.sum_mul, unitary_col_sq_sum, one_mul] at h
  rwa [entropy_eq_sum hA.isHermitian]


/-- Entropy is invariant under every unitary basis change. -/
theorem entropy_unitary_conj (U : Matrix.unitaryGroup ι ℂ)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Unitary.conjStarAlgAut ℂ _ U A) = entropy A := by
  have hφA : (Unitary.conjStarAlgAut ℂ _ U A).IsHermitian := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA
  have hm := StarAlgHomClass.map_cfc (S := ℂ)
    (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) Real.negMulLog A
    Real.continuous_negMulLog.continuousOn
    (show Continuous (fun P : Matrix ι ι ℂ ↦ (U : Matrix ι ι ℂ) * P * star U) by fun_prop)
    hA hφA
  unfold entropy
  calc
    _ = (Matrix.trace (Unitary.conjStarAlgAut ℂ _ U (cfc Real.negMulLog A))).re :=
      congrArg (fun P : Matrix ι ι ℂ ↦ P.trace.re) hm.symm
    _ = _ := congrArg Complex.re (trace_unitary_conj U _)

/-- The full matrix entropy, not just normalized-state entropy, is concave on
positive semidefinite matrices. -/
theorem concaveOn_entropy :
    ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosSemidef} entropy := by
  refine ⟨?_, ?_⟩
  · intro A hA B hB a b ha hb _
    exact (hA.smul ha).add (hB.smul hb)
  intro A hA B hB a b ha hb hab
  let C := a • A + b • B
  have hC : C.PosSemidef := (hA.smul ha).add (hB.smul hb)
  let U := hC.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  have hp (P : Matrix ι ι ℂ) (hP : P.PosSemidef) : (φ P).PosSemidef := by
    exact hP.mul_mul_conjTranspose_same (star U : Matrix ι ι ℂ)
  have hdiag : φ C = Matrix.diagonal (fun i ↦ (hC.isHermitian.eigenvalues i : ℂ)) := by
    exact hC.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hlin : φ C = a • φ A + b • φ B := by
    dsimp only [C]
    rw [map_add]
    congr 1 <;> exact (φ.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul _ _
  have hs (i : ι) :
      a * Real.negMulLog ((φ A) i i).re + b * Real.negMulLog ((φ B) i i).re ≤
        Real.negMulLog (hC.isHermitian.eigenvalues i) := by
    have he : hC.isHermitian.eigenvalues i = a * ((φ A) i i).re + b * ((φ B) i i).re := by
      have ht := congrArg (fun P : Matrix ι ι ℂ ↦ (P i i).re) (hdiag.symm.trans hlin)
      simpa using ht
    rw [he]
    exact Real.concaveOn_negMulLog.2
      ((Complex.nonneg_iff.mp (hp A hA).diag_nonneg).1)
      ((Complex.nonneg_iff.mp (hp B hB).diag_nonneg).1) ha hb hab
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hs i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hEA := entropy_le_diagonal (hp A hA)
  have hEB := entropy_le_diagonal (hp B hB)
  rw [entropy_unitary_conj (star U) hA.isHermitian] at hEA
  rw [entropy_unitary_conj (star U) hB.isHermitian] at hEB
  rw [entropy_eq_sum hC.isHermitian]
  exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hEA ha)
    (mul_le_mul_of_nonneg_left hEB hb)) hsum

end GAD

end

end OAI
