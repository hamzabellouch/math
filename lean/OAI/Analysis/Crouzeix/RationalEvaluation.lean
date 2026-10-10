import Mathlib
import OAI.Analysis.Crouzeix.NumericalRange

namespace OAI

/-! Holomorphic continuity, pole-free rational evaluation, and tensor norm bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem EntrywiseHolomorphic.continuousOn {m : ℕ} {U : Set ℂ} {F : ℂ → Coeff m}
    (hF : EntrywiseHolomorphic U F) : ContinuousOn F U := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (hF i j).continuousOn

theorem holomorphic_sup_attained [Nontrivial H] (A : Operator H)
    {m : ℕ} {U : Set ℂ} {F : ℂ → Coeff m}
    (hU : numericalClosure A ⊆ U) (hF : EntrywiseHolomorphic U F) :
    ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) F = ‖F z‖ :=
  supNorm_attained (isCompact_numericalClosure A) (numericalClosure_nonempty A)
    (hF.continuousOn.mono hU)

theorem isUnit_polynomial_aeval [CompleteSpace H] [Nontrivial H]
    (A : Operator H) (p : Polynomial ℂ)
    (hp : ∀ z ∈ numericalClosure A, p.eval z ≠ 0) :
    IsUnit (Polynomial.aeval A p) := by
  apply spectrum.isUnit_of_zero_notMem ℂ
  rw [spectrum.map_polynomial_aeval A p]
  rintro ⟨z, hz, heq⟩
  exact hp z (spectrum_subset_numericalClosure A hz) heq

theorem rational_denominators_isUnit [CompleteSpace H] [Nontrivial H]
    (A : Operator H) {m : ℕ} (R : RationalMatrix m)
    (hR : PolesOutside (numericalClosure A) R) :
    ∀ i j, IsUnit (Polynomial.aeval A (R i j).denom) :=
  fun i j => isUnit_polynomial_aeval A (R i j).denom (hR i j)

theorem rational_holomorphic_neighborhood {m : ℕ} {K : Set ℂ}
    (R : RationalMatrix m) (hR : PolesOutside K R) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) := by
  let U : Set ℂ := ⋂ i, ⋂ j, {z : ℂ | (R i j).denom.eval z ≠ 0}
  have hne : ∀ z ∈ U, ∀ i j, (R i j).denom.eval z ≠ 0 := by
    intro z hz i j
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hz i) j
  refine ⟨U, ?_, ?_, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_ne.preimage (R i j).denom.continuous
  · intro z hz
    exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun j => hR i j z hz))
  · intro i j
    simp only [matrixRationalFunction, RatFunc.eval, Polynomial.eval₂_id]
    exact DifferentiableOn.div (𝕜 := ℂ) (𝕜' := ℂ)
      (R i j).num.differentiableOn (R i j).denom.differentiableOn
      (fun z hz => hne z hz i j)

theorem rational_sup_attained [Nontrivial H] (A : Operator H)
    {m : ℕ} (R : RationalMatrix m) (hR : PolesOutside (numericalClosure A) R) :
    ∃ z ∈ numericalClosure A, supNorm (numericalClosure A) (matrixRationalFunction R) =
      ‖matrixRationalFunction R z‖ := by
  obtain ⟨U, _, hU, hF⟩ := rational_holomorphic_neighborhood R hR
  exact holomorphic_sup_attained A hU hF

theorem norm_tensorOperator_le (A : Operator H) {m : ℕ} (B : Coeff m) :
    ‖tensorOperator A B‖ ≤ ‖A‖ * ‖B‖ := by
  apply (tensorOperator A B).opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (tensorOperator A B).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro a
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe]
  exact ((TensorProduct.mapL A (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) B)).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le A (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) B))
      (norm_nonneg _))

@[simp]
theorem tensorOperator_zero_right (A : Operator H) (m : ℕ) :
    tensorOperator A (0 : Coeff m) = 0 := by
  apply norm_le_zero_iff.mp
  simpa using norm_tensorOperator_le A (0 : Coeff m)

end CrouzeixHilbert
end

end OAI
