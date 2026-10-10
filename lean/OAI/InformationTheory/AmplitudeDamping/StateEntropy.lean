import OAI.InformationTheory.AmplitudeDamping.PureRecursion

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem state_mixture (w : α → ℝ) (P : α → Matrix ι ι ℂ)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hP : ∀ a, IsState (P a)) :
    IsState (∑ a, w a • P a) := by
  constructor
  · rw [← Matrix.nonneg_iff_posSemidef]
    exact Finset.sum_nonneg (fun a _ ↦ Matrix.nonneg_iff_posSemidef.mpr ((hP a).1.smul (hw a)))
  · simp only [Matrix.trace_sum,Matrix.trace_smul,(hP _).2,Complex.real_smul,mul_one]
    exact_mod_cast hs

theorem spectral_pure_decomposition {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    P = ∑ a, hP.eigenvalues a • pure (fun i ↦ hP.eigenvectorUnitary i a) := by
  conv_lhs => rw [hP.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  ext i j
  simp only [Matrix.mul_apply,Matrix.star_apply,Matrix.sum_apply,
    Matrix.smul_apply,pure,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [diagonal_apply, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change hP.eigenvectorUnitary i a * (hP.eigenvalues a : ℂ) * star (hP.eigenvectorUnitary j a) =
    (hP.eigenvalues a : ℂ) * (hP.eigenvectorUnitary i a * star (hP.eigenvectorUnitary j a))
  ring

theorem spectral_weights_sum {P : Matrix ι ι ℂ} (hP : IsState P) :
    ∑ a, hP.1.isHermitian.eigenvalues a = 1 := by
  simpa using congrArg Complex.re
    (hP.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hP.2)

theorem spectral_vectors_mass {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (a : ι) :
    vecMass (fun i ↦ hP.eigenvectorUnitary i a) = 1 :=
  unitary_col_sq_sum hP.eigenvectorUnitary a

theorem channel_mixture (γ ν : ℝ) (n : ℕ) (w : α → ℝ) (P : α → QMatrix n) :
    channel γ ν n (∑ a, w a • P a) = ∑ a, w a • channel γ ν n (P a) := by
  simp only [channel,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]

def matrixPopulation {n : ℕ} (P : QMatrix n) (j : Fin n) : ℝ :=
  ∑ i, if i j = 1 then (P i i).re else 0

theorem matrixPopulation_pure {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    matrixPopulation (pure ψ) j = population ψ j := by
  simp [matrixPopulation,population,pure,Complex.mul_conj]

theorem matrixPopulation_mixture {n : ℕ} (w : α → ℝ) (P : α → QMatrix n) (j : Fin n) :
    matrixPopulation (∑ a, w a • P a) j = ∑ a, w a * matrixPopulation (P a) j := by
  simp only [matrixPopulation,Matrix.sum_apply,Complex.re_sum,Matrix.smul_apply,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem matrixPopulation_nonneg {n : ℕ} {P : QMatrix n} (hP : P.PosSemidef) (j : Fin n) :
    0 ≤ matrixPopulation P j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (Complex.nonneg_iff.mp hP.diag_nonneg).1
  · rfl

theorem matrixPopulation_le_trace {n : ℕ} {P : QMatrix n} (hP : P.PosSemidef) (j : Fin n) :
    matrixPopulation P j ≤ P.trace.re := by
  rw [Matrix.trace,Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact (Complex.nonneg_iff.mp hP.diag_nonneg).1

theorem matrixPopulation_mem {n : ℕ} {P : QMatrix n} (hP : IsState P) (j : Fin n) :
    matrixPopulation P j ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨matrixPopulation_nonneg hP.1 j, ?_⟩
  simpa only [hP.2,Complex.one_re] using matrixPopulation_le_trace hP.1 j

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def spectralFactor {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : Matrix ι ι ℂ :=
  fun i k ↦ (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ) * hA.isHermitian.eigenvectorUnitary i k

theorem spectralFactor_gram {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    gram (spectralFactor hA) = A := by
  conv_rhs => rw [spectral_pure_decomposition hA.isHermitian]
  ext i j
  simp only [gram,Matrix.mul_apply,Matrix.conjTranspose_apply,spectralFactor,
    star_mul,Matrix.sum_apply,Matrix.smul_apply,pure,Complex.real_smul,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro k _
  have hs : (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ)^2 =
      (hA.isHermitian.eigenvalues k : ℂ) := by exact_mod_cast Real.sq_sqrt (hA.eigenvalues_nonneg k)
  calc
    _ = (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ)^2 *
      (hA.isHermitian.eigenvectorUnitary i k * star (hA.isHermitian.eigenvectorUnitary j k)) := by
        simp only [Complex.star_def]; ring
    _ = _ := by rw [hs]; rfl

theorem spectralFactor_column {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (k : ι) :
    ∑ i, Complex.normSq (spectralFactor hA i k) = hA.isHermitian.eigenvalues k := by
  simp only [spectralFactor,Complex.normSq_mul,Complex.normSq_ofReal,← pow_two,
    Real.sq_sqrt (hA.eigenvalues_nonneg k),← Finset.mul_sum,unitary_col_sq_sum,mul_one]

theorem entropy_sum_le (A : α → Matrix ι ι ℂ) (hA : ∀ a, (A a).PosSemidef) :
    entropy (∑ a, A a) ≤ ∑ a, entropy (A a) := by
  let F : Matrix ι (α × ι) ℂ := fun i ak ↦ spectralFactor (hA ak.1) i ak.2
  have hgram : gram F = ∑ a, A a := by
    ext i j
    change (∑ ak : α × ι, spectralFactor (hA ak.1) i ak.2 *
      star (spectralFactor (hA ak.1) j ak.2)) = (∑ a, A a) i j
    simp only [Fintype.sum_prod_type,Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    exact congrArg (fun M : Matrix ι ι ℂ ↦ M i j) (spectralFactor_gram (hA a))
  have hdiag (ak : α × ι) : ((Fᴴ*F) ak ak).re = (hA ak.1).isHermitian.eigenvalues ak.2 := by
    change (∑ i, star (F i ak)*F i ak).re = _
    simp only [Complex.re_sum,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,F]
    exact spectralFactor_column (hA ak.1) ak.2
  rw [← hgram]
  change entropy (F*Fᴴ) ≤ _
  rw [entropy_mul_conjTranspose]
  have he := entropy_le_diagonal (Matrix.posSemidef_conjTranspose_mul_self F)
  simpa only [hdiag,Fintype.sum_prod_type,entropy_eq_sum (hA _).isHermitian] using he

theorem entropy_mixture_upper (w : α → ℝ) (A : α → Matrix ι ι ℂ)
    (hw : ∀ a, 0 ≤ w a) (hA : ∀ a, IsState (A a)) :
    entropy (∑ a, w a • A a) ≤ ∑ a, (w a*entropy (A a)+Real.negMulLog (w a)) := by
  have h := entropy_sum_le (fun a ↦ w a • A a) (fun a ↦ (hA a).1.smul (hw a))
  simpa only [entropy_smul _ (hA _).1.isHermitian,(hA _).2,Complex.one_re,mul_one] using h

end GAD

end

end OAI
