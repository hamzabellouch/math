import Mathlib
import OAI.MathematicalPhysics.BFSS.FrequencyComparison

namespace OAI

/-! Complex frequency eigenmodes and nonvanishing eigenvalues. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
open scoped ComplexConjugate
variable {N : ℕ}

def complexFrequency (K : FrequencyMatrix N) :
    Matrix (FrequencyIndex N) (FrequencyIndex N) ℂ :=
  fun r s => Complex.I*(K r s : ℂ)

lemma complexFrequency_hermitian (K : FrequencyMatrix N) (hK : K.transpose = -K) :
    (complexFrequency K).IsHermitian := by
  have hn (r s : FrequencyIndex N) : K s r = -K r s :=
    congrArg (fun A : FrequencyMatrix N => A r s) hK
  ext r s
  change conj (Complex.I*(K s r : ℂ)) = Complex.I*(K r s : ℂ)
  rw [map_mul,Complex.conj_I,Complex.conj_ofReal,hn,Complex.ofReal_neg]
  ring

lemma complexFrequency_eigenmode (K : FrequencyMatrix N) (hK : K.transpose = -K)
    (j : FrequencyIndex N) (r : FrequencyIndex N) :
    Complex.I*(∑ s, (K r s : ℂ)*
      ((complexFrequency_hermitian K hK).eigenvectorBasis j s)) =
      ((complexFrequency_hermitian K hK).eigenvalues j : ℂ)*
        ((complexFrequency_hermitian K hK).eigenvectorBasis j r) := by
  have h := congrFun ((complexFrequency_hermitian K hK).mulVec_eigenvectorBasis j) r
  simpa only [Matrix.mulVec,dotProduct,complexFrequency,Pi.smul_apply,
    Complex.real_smul,mul_assoc,Finset.mul_sum] using h

lemma complexFrequency_conjugate_mode (K : FrequencyMatrix N) (v : FrequencyIndex N → ℂ)
    (ω : ℝ) (hv : ∀ r, Complex.I*(∑ s, (K r s : ℂ)*v s) = (ω : ℂ)*v r) :
    ∀ r, Complex.I*(∑ s, (K r s : ℂ)*conj (v s)) = ((-ω : ℝ) : ℂ)*conj (v r) := by
  intro r
  have h := congrArg conj (hv r)
  simp only [map_mul,map_sum,Complex.conj_I,Complex.conj_ofReal] at h
  rw [Complex.ofReal_neg]
  linear_combination -h

variable (M : AlgebraData N)

theorem normal_frequency_complex_kernel (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) (v : FrequencyIndex N → ℂ)
    (hv : ∀ r, Complex.I*(∑ s, (M.normalFermionFrequency q r s : ℂ)*v s) = 0) : v = 0 := by
  have hz (r : FrequencyIndex N) :
      (∑ s, (M.normalFermionFrequency q r s : ℂ)*v s) = 0 :=
    (mul_eq_zero.mp (hv r)).resolve_left Complex.I_ne_zero
  let vr : EuclideanSpace ℝ (FrequencyIndex N) := WithLp.toLp 2 (fun r => (v r).re)
  let vi : EuclideanSpace ℝ (FrequencyIndex N) := WithLp.toLp 2 (fun r => (v r).im)
  have hr : BFSSSpinHalf.eucAlg (M.normalFermionFrequency q) vr = 0 := by
    apply PiLp.ext
    intro r
    have h := congrArg Complex.re (hz r)
    simpa only [BFSSSpinHalf.eucAlg_eq,Matrix.toLpLin_apply,Matrix.mulVec,
      dotProduct,vr,PiLp.zero_apply,Complex.re_sum,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      Complex.zero_re] using h
  have hi : BFSSSpinHalf.eucAlg (M.normalFermionFrequency q) vi = 0 := by
    apply PiLp.ext
    intro r
    have h := congrArg Complex.im (hz r)
    simpa only [BFSSSpinHalf.eucAlg_eq,Matrix.toLpLin_apply,Matrix.mulVec,
      dotProduct,vi,PiLp.zero_apply,Complex.im_sum,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      Complex.zero_im] using h
  have hvr := M.normalFermionFrequency_trivial_kernel q hq vr hr
  have hvi := M.normalFermionFrequency_trivial_kernel q hq vi hi
  funext r
  apply Complex.ext
  · exact congrArg (fun w : EuclideanSpace ℝ (FrequencyIndex N) => w r) hvr
  · exact congrArg (fun w : EuclideanSpace ℝ (FrequencyIndex N) => w r) hvi

theorem normal_frequency_eigenvalues_ne_zero (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) (j : FrequencyIndex N) :
    (complexFrequency_hermitian (M.normalFermionFrequency q)
      (M.normalFermionFrequency_skew q)).eigenvalues j ≠ 0 := by
  intro hz
  have hH := complexFrequency_hermitian (M.normalFermionFrequency q)
    (M.normalFermionFrequency_skew q)
  have hm := complexFrequency_eigenmode (M.normalFermionFrequency q)
    (M.normalFermionFrequency_skew q) j
  have hm0 (r : FrequencyIndex N) :
      Complex.I*(∑ s, (M.normalFermionFrequency q r s : ℂ)*(hH.eigenvectorBasis j s)) = 0 := by
    have h := hm r
    rw [hz] at h
    simpa only [Complex.ofReal_zero,zero_mul] using h
  have hb := M.normal_frequency_complex_kernel q hq (hH.eigenvectorBasis j) hm0
  have he : hH.eigenvectorBasis j = 0 := by
    apply PiLp.ext
    exact congrFun hb
  exact (hH.eigenvectorBasis.toBasis.ne_zero j) he

end
end BFSSQuantum.AlgebraData

end OAI
