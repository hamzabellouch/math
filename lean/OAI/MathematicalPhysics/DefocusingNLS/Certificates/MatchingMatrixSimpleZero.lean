import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingMatrix
import Mathlib.Analysis.Analytic.Order

namespace OAI

/-! A simple zero of the full matching determinant excludes a first
differentiated matching chain. The adjugate identity handles all four columns
without choosing a possibly singular minor. -/

open Matrix
namespace DefocusingNLS

private theorem matrix_det_analyticAt {n : Type*} [Fintype n] [DecidableEq n]
    (M : ℂ → Matrix n n ℂ) (z : ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) :
    AnalyticAt ℂ (fun w => (M w).det) z := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hM (σ i) i

private theorem matrix_adjugate_analyticAt {n : Type*} [Fintype n] [DecidableEq n]
    (M : ℂ → Matrix n n ℂ) (z : ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) (i j : n) :
    AnalyticAt ℂ (fun w => (M w).adjugate i j) z := by
  simp_rw [Matrix.adjugate_apply]
  apply matrix_det_analyticAt
  intro k l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simpa only [Matrix.updateRow_ne hk] using hM k l

private theorem matrix_mulVec_hasDerivAt {n : Type*} [Fintype n]
    (M : ℂ → Matrix n n ℂ) (dM : Matrix n n ℂ) (z : ℂ)
    (hM : ∀ i j, HasDerivAt (fun w => M w i j) (dM i j) z) (u : n → ℂ) (i : n) :
    HasDerivAt (fun w => (M w *ᵥ u) i) ((dM *ᵥ u) i) z := by
  simpa only [Matrix.mulVec, dotProduct] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hM i j).mul_const (u j)))

theorem matchingMatrix_simple_zero_no_chain {n : Type*} [Fintype n] [DecidableEq n]
    (M : ℂ → Matrix n n ℂ) (z : ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z)
    (hsimple : analyticOrderAt (fun w => (M w).det) z = 1)
    (u v : n → ℂ) (hu : u ≠ 0) (hkernel : M z *ᵥ u = 0) :
    M z *ᵥ v + (fun i j => deriv (fun w => M w i j) z) *ᵥ u ≠ 0 := by
  classical
  let dM : Matrix n n ℂ := fun i j => deriv (fun w => M w i j) z
  let D : ℂ → ℂ := fun w => (M w).det
  have hD : AnalyticAt ℂ D z := matrix_det_analyticAt M z hM
  have hz : D z = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero
    (by rw [show analyticOrderAt D z = 1 from hsimple]; exact one_ne_zero)
  have hdo : analyticOrderAt (deriv D) z = 0 :=
    analyticOrderAt_deriv_of_pos hD (n := 0) (by simpa using hsimple)
  have hd : deriv D z ≠ 0 := hD.deriv.analyticOrderAt_eq_zero.mp hdo
  have hMd (i j : n) : HasDerivAt (fun w => M w i j) (dM i j) z :=
    (hM i j).differentiableAt.hasDerivAt
  have hAdj (w : ℂ) (x : n → ℂ) :
      (M w).adjugate *ᵥ (M w *ᵥ x) = D w • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro hchain
  have hzero : (M z).adjugate *ᵥ (dM *ᵥ u) = 0 := by
    have he := congrArg (fun x => (M z).adjugate *ᵥ x) hchain
    rw [Matrix.mulVec_add, hAdj, hz, zero_smul, zero_add, Matrix.mulVec_zero] at he
    exact he
  have hder (i : n) : HasDerivAt (fun w => ((M w).adjugate *ᵥ (M w *ᵥ u)) i)
      (((M z).adjugate *ᵥ (dM *ᵥ u)) i) z := by
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((matrix_adjugate_analyticAt M z hM i j).differentiableAt.hasDerivAt).mul
        (matrix_mulVec_hasDerivAt M dM z hMd u j))
    simp only [hkernel, Pi.zero_apply, mul_zero, zero_add] at hh
    convert! hh using 1
  have he (i : n) : deriv D z * u i = 0 := by
    have hl := hder i
    simp only [hAdj, Pi.smul_apply, smul_eq_mul, hzero, Pi.zero_apply] at hl
    exact (hD.differentiableAt.hasDerivAt.mul_const (u i)).unique hl
  apply hu
  funext i
  exact (mul_eq_zero.mp (he i)).resolve_left hd

end DefocusingNLS

end OAI
