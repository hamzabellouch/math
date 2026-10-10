import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FiberMap

namespace OAI

section
section
section
section
noncomputable section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian FourierTransform
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma distribution_derivatives_commute (v w : E) (u : 𝓢'(E,F)) :
    ∂_{v} (∂_{w} u) = ∂_{w} (∂_{v} u) := by
  apply (FourierTransform.fourierEquiv ℂ 𝓢'(E,F)).injective
  change 𝓕 (∂_{v} (∂_{w} u)) = 𝓕 (∂_{w} (∂_{v} u))
  simp only [fourier_lineDerivOp_eq, map_smul]
  congr 2
  rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  rw [mul_comm]

omit [CompleteSpace F] in
lemma helmholtz_derivative (v : E) (u : 𝓢'(E,F)) :
    EuclideanGreen.helmholtz (∂_{v} u) = ∂_{v} (EuclideanGreen.helmholtz u) := by
  rw [← EuclideanGreen.bessel_two_eq_helmholtz, ← EuclideanGreen.bessel_two_eq_helmholtz]
  apply (FourierTransform.fourierEquiv ℂ 𝓢'(E,F)).injective
  change 𝓕 (besselPotential E F 2 (∂_{v} u)) = 𝓕 (∂_{v} (besselPotential E F 2 u))
  simp only [fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
    fourier_lineDerivOp_eq, map_smul]
  congr 1
  rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  rw [mul_comm]

def principalDerivativeError (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (v : E) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  ∑ i, ∑ j, smulLeftCLM F (∂_{v} (a i j) : 𝓢(E,ℂ))
    (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u))

omit [CompleteSpace F] in
lemma perturbedHelmholtz_derivative
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (v : E) (u : 𝓢'(E,F)) :
    ∂_{v} (perturbedHelmholtz a u) =
      perturbedHelmholtz a (∂_{v} u) + principalDerivativeError a v u := by
  simp only [perturbedHelmholtz, differentialPerturbation,
    LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_sum,
    distribution_derivative_product, Finset.sum_add_distrib,
    principalDerivativeError, ← helmholtz_derivative]
  have hc (i j : basisIndex E) :
      ∂_{v} (∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} u)) =
      ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E j} (∂_{v} u)) := by
    rw [distribution_derivatives_commute v, distribution_derivatives_commute v]
  simp only [hc]
  abel

lemma principalDerivativeError_memSobolev (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (v : E)
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+2) 2 u) :
    MemSobolev n 2 (principalDerivativeError a v u) := by
  apply memSobolev_sum
  intro i _
  apply memSobolev_sum
  intro j _
  apply memSobolev_nat_product
  convert hu.lineDerivOp.lineDerivOp using 1
  ring

theorem principal_H1_bootstrap (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1) {u : 𝓢'(E,F)}
    (hu : MemSobolev 1 2 u)
    (hf : MemSobolev n 2 (perturbedHelmholtz a u)) :
    MemSobolev ((n:ℝ)+2) 2 u := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero, zero_add] at hf ⊢
    exact weak_H1_regular a hweak hstrong hu hf
  | succ n ih =>
    have hf' : MemSobolev n 2 (perturbedHelmholtz a u) :=
      hf.mono (by exact_mod_cast Nat.le_succ n)
    have hu2 := ih hu hf'
    have hd (i : basisIndex E) :
        MemSobolev ((n:ℝ)+2) 2 (∂_{stdOrthonormalBasis ℝ E i} u) := by
      have hd1 : MemSobolev 1 2 (∂_{stdOrthonormalBasis ℝ E i} u) :=
        hu2.lineDerivOp.mono (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hdf : MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i}
          (perturbedHelmholtz a u)) := by
        convert hf.lineDerivOp using 1
        simp
      have he := principalDerivativeError_memSobolev n a
        (stdOrthonormalBasis ℝ E i) hu2
      have hr := hdf.sub he
      rw [perturbedHelmholtz_derivative, add_sub_cancel_right] at hr
      exact ih hd1 hr
    have h := memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) hu2 hd
    convert h using 1
    push_cast
    ring

theorem matrix_H1_bootstrap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hweak : ‖perturbationNegOne (F := F) a‖ < 1)
    (hstrong : ‖perturbation (F := F) 0 a‖ < 1)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) {u : 𝓢'(E,F)}
    (hu : MemSobolev 1 2 u)
    (hf : MemSobolev n 2 (perturbedHelmholtz a u + matrixLowerOrder b L v c K u)) :
    MemSobolev ((n:ℝ)+2) 2 u := by
  induction n with
  | zero =>
    have hu' : MemSobolev ((0:ℕ)+1:ℝ) 2 u := by simpa using hu
    have hl := matrixLowerOrder_memSobolev 0 b L v c K hu'
    have hp := hf.sub hl
    rw [add_sub_cancel_right] at hp
    exact principal_H1_bootstrap 0 a hweak hstrong hu hp
  | succ n ih =>
    have hu2 := ih (hf.mono (by exact_mod_cast Nat.le_succ n))
    have hu' : MemSobolev ((n+1:ℕ)+1:ℝ) 2 u := by
      convert hu2 using 1
      push_cast
      ring
    have hl := matrixLowerOrder_memSobolev (n+1) b L v c K hu'
    have hp := hf.sub hl
    rw [add_sub_cancel_right] at hp
    exact principal_H1_bootstrap (n+1) a hweak hstrong hu hp

end TamingCompatibility.HilbertSobolev

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace

end
end
end
end
end
end
end

end OAI
