import OAI.MeasureTheory.Falconer.Fourier.ParametricJets
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-!
# Quantitative finite-derivative bounds for stationary jets

The Laplacian is a fixed finite sum of second directional derivatives.
Expressing that contraction as a continuous linear map gives bounds for
all mixed Fréchet derivatives, without replacing them by separate bounds
on a single chart coordinate. Vertical unit vectors in a parameter/tangent
product give the partial Laplacian used by the actual stationary operators.
-/

namespace Falconer
open scoped BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance
noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℂ) := inferInstance

noncomputable def directionalLaplacianTrace {n : ℕ} (v : Fin n → E) :
    (E →L[ℝ] E →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ∑ i : Fin n, (ContinuousLinearMap.apply ℝ ℂ (v i)).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℂ) (v i))

@[simp] theorem directionalLaplacianTrace_apply {n : ℕ} (v : Fin n → E)
    (T : E →L[ℝ] E →L[ℝ] ℂ) : directionalLaplacianTrace v T = ∑ i : Fin n, T (v i) (v i) := by
  simp [directionalLaplacianTrace]

theorem directionalLaplacianTrace_norm_le {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖directionalLaplacianTrace v‖ ≤ n := by
  apply (directionalLaplacianTrace v).opNorm_le_bound (Nat.cast_nonneg n)
  intro T
  rw [directionalLaplacianTrace_apply]
  calc
    ‖∑ i : Fin n, T (v i) (v i)‖ ≤ ∑ i : Fin n, ‖T (v i) (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖T‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖T (v i) (v i)‖ ≤ ‖T (v i)‖ * ‖v i‖ := (T (v i)).le_opNorm _
        _ ≤ (‖T‖ * ‖v i‖) * ‖v i‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖T‖ := by
          simpa only [mul_one] using mul_le_mul
            (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg T))
            (hv i) (norm_nonneg (v i)) (mul_nonneg (norm_nonneg T) zero_le_one)
    _ = (n : ℝ) * ‖T‖ := by simp

noncomputable def directionalLaplacian {n : ℕ} (v : Fin n → E) (f : E → ℂ) : E → ℂ :=
  fun x => directionalLaplacianTrace v (fderiv ℝ (fderiv ℝ f) x)

theorem directionalLaplacian_contDiff {n : ℕ} (v : Fin n → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (directionalLaplacian v f) := by
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    h₁.fderiv_right (by simp)
  exact (directionalLaplacianTrace v).contDiff.comp hd

theorem directionalLaplacian_derivative_bound {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (directionalLaplacian v f) x‖ ≤
      (n : ℝ) * ‖iteratedFDeriv ℝ (k+2) f x‖ := by
  have h₁ : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    h₁.fderiv_right (by simp)
  change ‖iteratedFDeriv ℝ k
    ((directionalLaplacianTrace v) ∘ (fderiv ℝ (fderiv ℝ f))) x‖ ≤ _
  rw [(directionalLaplacianTrace v).iteratedFDeriv_comp_left hd.contDiffAt (by simp)]
  have h := (directionalLaplacianTrace v).norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ k (fderiv ℝ (fderiv ℝ f)) x)
  rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv] at h
  exact h.trans (mul_le_mul_of_nonneg_right (directionalLaplacianTrace_norm_le v hv)
    (norm_nonneg _))

theorem iteratedDirectionalLaplacian_contDiff {n : ℕ} (v : Fin n → E) {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ ((directionalLaplacian v)^[j] f) := by
  induction j with
  | zero => exact hf
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      exact directionalLaplacian_contDiff v hj

/-- Every mixed derivative of order `k` of the `j`th directional Laplacian
uses only the amplitude's derivative of order `k+2j`, with loss `n^j`. -/
theorem iteratedDirectionalLaplacian_derivative_bound {n : ℕ} (v : Fin n → E)
    (hv : ∀ i, ‖v i‖ ≤ 1) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (j k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k ((directionalLaplacian v)^[j] f) x‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) f x‖ := by
  induction j generalizing k with
  | zero => simp
  | succ j hj =>
      rw [Function.iterate_succ_apply']
      have h₁ := directionalLaplacian_derivative_bound v hv
        (iteratedDirectionalLaplacian_contDiff v hf j) k x
      have h₂ := mul_le_mul_of_nonneg_left (hj (k+2)) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
      apply (h₁.trans h₂).trans_eq
      rw [show k+2+2*j = k+2*(j+1) by omega, pow_succ]
      ring

theorem directionalLaplacian_basis {n : ℕ} (f : Space n → ℂ) :
    directionalLaplacian (EuclideanSpace.basisFun (Fin n) ℝ) f = Laplacian.laplacian f := by
  funext x
  rw [directionalLaplacian, directionalLaplacianTrace_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply]
  rfl

theorem euclidean_iterated_laplacian_derivative_bound {n : ℕ} {f : Space n → ℂ}
    (hf : ContDiff ℝ ∞ f) (j k : ℕ) (x : Space n) :
    ‖iteratedFDeriv ℝ k
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] f) x‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) f x‖ := by
  have he : directionalLaplacian (EuclideanSpace.basisFun (Fin n) ℝ) =
      (Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ)) := by
    funext g
    exact directionalLaplacian_basis g
  rw [← he]
  apply iteratedDirectionalLaplacian_derivative_bound _ _ hf
  intro i
  simp

section Parameters
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

noncomputable def verticalDirections (n : ℕ) : Fin n → P × Space n :=
  fun i => (0, (EuclideanSpace.basisFun (Fin n) ℝ) i)

omit [NormedSpace ℝ P] in
theorem verticalDirections_norm {n : ℕ} (i : Fin n) :
    ‖(verticalDirections n i : P × Space n)‖ ≤ 1 := by
  simp [verticalDirections, Prod.norm_def]

theorem directionalLaplacian_vertical {n : ℕ} {F : P × Space n → ℂ}
    (hF : ContDiff ℝ ∞ F) (p : P) (x : Space n) :
    directionalLaplacian (verticalDirections n) F (p,x) =
      Laplacian.laplacian (fun y => F (p,y)) x := by
  let g : P × Space n → ℂ := fun z => F ((p,0)+z)
  have hg : ContDiff ℝ ∞ g := hF.comp (contDiff_const.add contDiff_id)
  have hd := (ContinuousLinearMap.inr ℝ P (Space n)).iteratedFDeriv_comp_right
    hg x (by simp : (2 : ℕ∞ω) ≤ ∞)
  have heq : g ∘ ContinuousLinearMap.inr ℝ P (Space n) = fun y => F (p,y) := by
    funext y
    simp [g]
  rw [heq] at hd
  have hshift : iteratedFDeriv ℝ 2 g (0,x) = iteratedFDeriv ℝ 2 F (p,x) := by
    simpa only [g, Prod.mk_add_mk, add_zero, zero_add] using
      (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := F) 2 (p,0) (0,x))
  change iteratedFDeriv ℝ 2 (fun y => F (p,y)) x =
    (iteratedFDeriv ℝ 2 g (0,x)).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ P (Space n)) at hd
  rw [hshift] at hd
  rw [directionalLaplacian, directionalLaplacianTrace_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_two_apply]
  rfl

theorem iteratedDirectionalLaplacian_vertical {n : ℕ} {F : P × Space n → ℂ}
    (hF : ContDiff ℝ ∞ F) (j : ℕ) (p : P) (x : Space n) :
    ((directionalLaplacian (verticalDirections n))^[j] F) (p,x) =
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (p,y))) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [directionalLaplacian_vertical
        (iteratedDirectionalLaplacian_contDiff _ hF j)]
      exact congrArg (fun g : Space n → ℂ => Laplacian.laplacian g x) (funext hj)

/-- The mixed derivative estimate needed for direction-dependent chart jets.
The order is exactly `k+2j`, and the constant is `n^j`. -/
theorem partialIteratedLaplacian_derivative_bound {n : ℕ} {F : P × Space n → ℂ}
    (hF : ContDiff ℝ ∞ F) (j k : ℕ) (z : P × Space n) :
    ‖iteratedFDeriv ℝ k (fun q : P × Space n =>
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (q.1,y))) q.2) z‖ ≤
      (n : ℝ)^j * ‖iteratedFDeriv ℝ (k+2*j) F z‖ := by
  have heq : (fun q : P × Space n =>
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
        (fun y => F (q.1,y))) q.2) =
      (directionalLaplacian (verticalDirections n))^[j] F := by
    funext q
    exact (iteratedDirectionalLaplacian_vertical hF j q.1 q.2).symm
  rw [heq]
  exact iteratedDirectionalLaplacian_derivative_bound _ verticalDirections_norm hF j k z

end Parameters

end Falconer

end OAI
