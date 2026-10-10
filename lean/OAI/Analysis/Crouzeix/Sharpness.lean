import Mathlib
import OAI.Analysis.Crouzeix.RationalEvaluation

namespace OAI

/-! A two-dimensional operator with sharp constant two. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def sharpOperator : Operator (EuclideanSpace ℂ (Fin 2)) :=
  (2 : ℂ) • InnerProductSpace.rankOne ℂ
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)

def sharpCoefficients : Fin 2 → Coeff 1 := ![0, 1]

theorem norm_sharpOperator : ‖sharpOperator‖ = 2 := by
  norm_num [sharpOperator, norm_smul, InnerProductSpace.norm_rankOne,
    PiLp.norm_single]

theorem sharpOperator_apply (x : EuclideanSpace ℂ (Fin 2)) :
    sharpOperator x = (2 * x 1) • EuclideanSpace.single 0 1 := by
  simp [sharpOperator, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left,
    smul_smul]

theorem sharpOperator_inner_norm (x : EuclideanSpace ℂ (Fin 2)) :
    ‖⟪x, sharpOperator x⟫_ℂ‖ = 2 * ‖x 0‖ * ‖x 1‖ := by
  rw [sharpOperator_apply, inner_smul_right, EuclideanSpace.inner_single_right]
  simp only [one_mul, norm_mul, Complex.norm_conj]
  norm_num
  ring

theorem sharpOperator_numerical_le {z : ℂ} (hz : z ∈ numericalRange sharpOperator) :
    ‖z‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  have hs := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_two, hx, one_pow] at hs
  rw [sharpOperator_inner_norm]
  nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖)]

theorem sharpOperator_numerical_attains :
    ∃ z ∈ numericalRange sharpOperator, ‖z‖ = 1 := by
  let v : EuclideanSpace ℂ (Fin 2) :=
    EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
  have hv0 : v 0 = 1 := by simp [v]
  have hv1 : v 1 = 1 := by simp [v]
  have hv : ‖v‖ ≠ 0 := by
    intro h
    have hh := congrArg (fun w : EuclideanSpace ℂ (Fin 2) => w 0) (norm_eq_zero.mp h)
    simp [hv0] at hh
  let x : EuclideanSpace ℂ (Fin 2) := (‖v‖ : ℂ)⁻¹ • v
  have hx : ‖x‖ = 1 := by simp [x, norm_smul, hv]
  have heq : x 0 = x 1 := by simp [x, hv0, hv1]
  refine ⟨⟪x, sharpOperator x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
  rw [sharpOperator_inner_norm, heq]
  have hs := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_two, hx, one_pow, heq] at hs
  nlinarith

@[simp]
theorem sharp_matrixPolynomial (z : ℂ) :
    matrixPolynomial (d := 1) sharpCoefficients z = z • (1 : Coeff 1) := by
  simp [matrixPolynomial, sharpCoefficients, Fin.sum_univ_two]

@[simp]
theorem sharp_polynomialEval : polynomialEval sharpOperator (d := 1) sharpCoefficients =
    tensorOperator sharpOperator (1 : Coeff 1) := by
  simp [polynomialEval, sharpCoefficients, Fin.sum_univ_two]

theorem sharpConstant : SharpConstant := by
  refine ⟨sharpOperator, sharpCoefficients, ?_, ?_⟩
  · apply le_antisymm
    · apply supNorm_le (by norm_num)
      intro z hz
      simpa [norm_smul] using sharpOperator_numerical_le hz
    · obtain ⟨z, hz, hzn⟩ := sharpOperator_numerical_attains
      have hbK := supNorm_bddAbove (isCompact_numericalClosure sharpOperator)
        (continuous_matrixPolynomial (d := 1) sharpCoefficients).continuousOn
      have hbW : BddAbove (insert 0 ((fun z => ‖matrixPolynomial (d := 1) sharpCoefficients z‖) ''
          numericalRange sharpOperator)) :=
        hbK.mono (Set.insert_subset_insert (Set.image_mono subset_closure))
      simpa [norm_smul, hzn] using norm_le_supNorm hbW hz
  · rw [sharp_polynomialEval]
    apply le_antisymm
    · simpa [norm_sharpOperator] using norm_tensorOperator_le sharpOperator (1 : Coeff 1)
    · let e : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1
      let f : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1
      let w : Amplification (EuclideanSpace ℂ (Fin 2)) 1 := ↑(e ⊗ₜ[ℂ] f)
      have hw : ‖w‖ ≤ 1 := by simp [w, e, f]
      have hl := (tensorOperator sharpOperator (1 : Coeff 1)).unit_le_opNorm w hw
      have he : ‖sharpOperator e‖ = 2 := by
        simp [sharpOperator_apply, e, norm_smul]
      simpa [w, f, tensorOperator, ContinuousLinearMap.completion_apply_coe, he] using hl

end CrouzeixHilbert
end

end OAI
