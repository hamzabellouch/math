import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Tactic.FinCases
import OAI.Geometry.NodalSets.Elliptic.SeedPolynomialDerivatives

namespace OAI

namespace Yau.Target
open scoped ContDiff
open Laplacian InnerProductSpace
noncomputable section

lemma seed_second_eq_iterated {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SeedAmbient → F) (hf : ContDiff ℝ ∞ f) (x v w : SeedAmbient) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w = iteratedFDeriv ℝ 2 f x ![w,v] := by
  have hd := (hf.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiable (by simp) x
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  rw [h.fderiv,iteratedFDeriv_two_apply]
  simp

lemma seedZ1_basis (i : Fin 5) : seedZ1 (EuclideanSpace.basisFun (Fin 5) ℝ i) =
    if i = 0 then 1 else if i = 1 then Complex.I else 0 := by
  fin_cases i <;> simp [seedZ1_apply,EuclideanSpace.basisFun_apply]

lemma seedZ2_basis (i : Fin 5) : seedZ2 (EuclideanSpace.basisFun (Fin 5) ℝ i) =
    if i = 2 then 1 else if i = 3 then Complex.I else 0 := by
  fin_cases i <;> simp [seedZ2_apply,EuclideanSpace.basisFun_apply]

lemma seedQuadratic_isotropic (x : SeedAmbient) :
    ∑ i, (seedQuadraticDerivative x (EuclideanSpace.basisFun (Fin 5) ℝ i))^2 = 0 := by
  simp only [seedQuadraticDerivative,add_apply,smul_apply,smul_eq_mul]
  simp_rw [seedZ1_basis,seedZ2_basis]
  simp [Fin.sum_univ_succ,mul_pow,Complex.I_sq]

lemma seedQuadratic_trace :
    ∑ i, (seedZ2 (EuclideanSpace.basisFun (Fin 5) ℝ i) *
      seedZ1 (EuclideanSpace.basisFun (Fin 5) ℝ i) +
      seedZ1 (EuclideanSpace.basisFun (Fin 5) ℝ i) *
      seedZ2 (EuclideanSpace.basisFun (Fin 5) ℝ i)) = 0 := by
  simp_rw [seedZ1_basis,seedZ2_basis]
  simp [Fin.sum_univ_succ]

lemma ambientComplexSeed_laplacian (N : ℕ) : Δ (ambientComplexSeed N) = 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 5) ℝ)]
  funext x
  simp_rw [← seed_second_eq_iterated _ (ambientComplexSeed_contDiff N),ambientComplexSeed_second]
  simp_rw [mul_assoc ((N:ℂ) * ((N-1:ℕ):ℂ) * seedQuadratic x^(N-1-1)),← pow_two]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    seedQuadratic_isotropic,seedQuadratic_trace]
  simp

lemma ambientRealSeed_laplacian (N : ℕ) : Δ (ambientRealSeed N) = 0 := by
  funext x
  have hc : ContDiffAt ℝ 2 (ambientComplexSeed N) x :=
    ((ambientComplexSeed_contDiff N).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
  change Δ (Complex.reCLM ∘ ambientComplexSeed N) x = 0
  rw [hc.laplacian_CLM_comp_left,ambientComplexSeed_laplacian]
  simp

lemma ambientRealSeed_harmonic (N : ℕ) : HarmonicOnNhd (ambientRealSeed N) Set.univ := by
  intro x hx
  exact ⟨((ambientRealSeed_contDiff N).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    Filter.EventuallyEq.of_eq (ambientRealSeed_laplacian N)⟩

end
end Yau.Target

end OAI
