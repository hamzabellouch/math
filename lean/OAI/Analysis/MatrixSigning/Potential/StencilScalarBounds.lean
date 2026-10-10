import Mathlib
import OAI.Analysis.MatrixSigning.Potential.RationalBasis

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Matrix
open scoped BigOperators ContDiff

variable {N : ℕ}

lemma stencil_scalar_bounds {a M n h : ℝ} (ha : 0 < a) (hM : 1 ≤ M)
    (hn : 1 ≤ n) (hh : 0 < h) (hh1 : h ≤ 1) (hhsmall : h ≤ a/(64*M*n)) :
    M*h^2/6+(a*h^2/(128*n))/h ≤ a/8 ∧
    M*h/3+4*(a*h^2/(128*n))/h^2 ≤ 7*a/(192*n) ∧
    (4/3:ℝ)*M*h+(a*h^2/(128*n))/h^2 ≤ 7*a/(192*n) := by
  have hn0 : 0 < n := by linarith
  have hMp : 0 < M := by linarith
  have hs : M*h ≤ a/(64*n) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<64*n)).mpr
    have ht := (le_div_iff₀ (by positivity : (0:ℝ)<64*M*n)).mp hhsmall
    nlinarith
  have he1 : (a*h^2/(128*n))/h = a*h/(128*n) := by field_simp
  have he2 : (a*h^2/(128*n))/h^2 = a/(128*n) := by field_simp
  have he3 : 4*(a*h^2/(128*n))/h^2 = a/(32*n) := by field_simp;ring
  rw [he1,he2,he3]
  have hs0 : M*h ≤ a/64 := hs.trans (by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<64*n)).mpr
    nlinarith)
  have hs2 : M*h^2 ≤ a/64 := by
    have h0 : 0 ≤ M*h := by positivity
    have ht := mul_le_mul_of_nonneg_left hh1 h0
    nlinarith
  have he : a*h/(128*n) ≤ a/128 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<128*n)).mpr
    nlinarith
  refine ⟨by linarith,?_,?_⟩
  · have he : a/(64*n)/3+a/(32*n)=7*a/(192*n) := by field_simp;ring
    calc
      _ ≤ a/(64*n)/3+a/(32*n) := by linarith
      _ = _ := he
  · have he : (4/3:ℝ)*(a/(64*n))+a/(128*n)=11*a/(384*n) := by field_simp;ring
    calc
      _ ≤ (4/3:ℝ)*(a/(64*n))+a/(128*n) := by linarith
      _ = 11*a/(384*n) := he
      _ ≤ 7*a/(192*n) := by
        have : 7*a/(192*n)-11*a/(384*n)=a/(128*n) := by field_simp;ring
        have hp : 0 ≤ a/(128*n) := by positivity
        linarith

theorem computed_stencil_accuracy [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℚ)
    {h : ℚ} {a M : ℝ} (ha : 0 < a) (hM1 : 1 ≤ M) (hh : 0<h)
    (hh1 : (h:ℝ) ≤ 1) (hhsmall : (h:ℝ) ≤ a/(64*M*N))
    (hf : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ContDiffAt ℝ 3 f y)
    (hM : ∀ y,‖y-pointCast x‖ ≤ 2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 3 (fun t : ℝ => f (y+t • u)) 0| ≤ M)
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) →
      |(query y:ℝ)-f (pointCast y)| ≤ a*(h:ℝ)^2/(128*N)) :
    (∀ i,|(stencilGradient query x h i:ℝ)-fderiv ℝ f (pointCast x) (realBasis i)| ≤ a/8) ∧
    (∀ i j,|(stencilHessian query x h i j:ℝ)-
      fderiv ℝ (fderiv ℝ f) (pointCast x) (realBasis i) (realBasis j)| ≤ 7*a/(192*N)) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have he : 0 ≤ a*(h:ℝ)^2/(128*N) := by positivity
  have hs := stencil_scalar_bounds ha hM1 hNr (by exact_mod_cast hh) hh1 hhsmall
  constructor
  · intro i
    exact (stencilGradient_error query f x h i hh he hf hM hquery).trans hs.1
  · intro i j
    by_cases hij : i=j
    · subst j
      exact (stencilHessian_diagonal_error query f x h i hh he hf hM hquery).trans hs.2.1
    · exact (stencilHessian_mixed_error query f x h i j hij hh hf hM hquery).trans hs.2.2

lemma linear_basis_expansion (L : (Fin N → ℝ) →L[ℝ] ℝ) (u : Fin N → ℝ) :
    L u = ∑ i,L (realBasis i)*u i := by
  have hu : u=∑ i,u i • realBasis i := by
    ext j
    simp [realBasis,Pi.single_apply]
  conv_lhs => rw [hu]
  simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

lemma bilinear_basis_expansion (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ)
    (u : Fin N → ℝ) : B u u=∑ i,∑ j,B (realBasis i) (realBasis j)*u i*u j := by
  rw [linear_basis_expansion (B u) u]
  have hb j : B u (realBasis j)=∑ i,B (realBasis i) (realBasis j)*u i := by
    exact linear_basis_expansion ((ContinuousLinearMap.apply ℝ ℝ (realBasis j)).comp B) u
  simp_rw [hb,Finset.sum_mul]
  exact Finset.sum_comm

theorem stencil_quadratic_accuracy (H : Matrix (Fin N) (Fin N) ℚ)
    (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] ℝ) {a : ℝ} (ha : 0 ≤ a)
    (herr : ∀ i j,|(H i j:ℝ)-B (realBasis i) (realBasis j)| ≤ 7*a/(192*N))
    (u : EuclideanSpace ℝ (Fin N)) :
    |u ⬝ᵥ ((H.map fun t : ℚ => (t:ℝ))*ᵥ u)-B u u| ≤ a/16*‖u‖^2 := by
  have hn : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hb : 0 ≤ 7*a/(192*N) := by positivity
  have he := quadratic_entrywise_error
    (fun i j => (H i j:ℝ)-B (realBasis i) (realBasis j)) u hb herr
  have heq : u ⬝ᵥ ((H.map fun t : ℚ => (t:ℝ))*ᵥ u)-B u u=
      ∑ i,∑ j,((H i j:ℝ)-B (realBasis i) (realBasis j))*u i*u j := by
    rw [bilinear_basis_expansion]
    simp only [dotProduct,mulVec,Matrix.map_apply,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  apply he.trans
  by_cases hN : N=0
  · simp only [hN,Nat.cast_zero,mul_zero,div_zero,zero_mul]
    positivity
  · have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast hN
    have hc : (N:ℝ)*(7*a/(192*N))=7*a/192 := by field_simp
    rw [hc]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end CurrentKS.Difference

end OAI
