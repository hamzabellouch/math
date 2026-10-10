import OAI.Analysis.KadisonKastler.ContractionPolarFactor
import Mathlib.Analysis.InnerProductSpace.Trace

namespace OAI

/-! # Finite operator coefficient duality

The polar factor and a positive rank-one decomposition give vector
coefficients whose two square sums are bounded by the functional norm.
This is the finite-dimensional part of the commutant distance formula.
-/

namespace KadisonKastler

open InnerProductSpace
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A finite sum of vector coefficient functionals on bounded operators. -/
def finiteOperatorCoefficient {ι : Type*} [Fintype ι] (x y : ι → E) :
    (E →L[ℂ] E) →L[ℂ] ℂ :=
  ∑ i, (innerSL ℂ (y i)).comp (ContinuousLinearMap.apply ℂ E (x i))

omit [CompleteSpace E] in
@[simp]
theorem finiteOperatorCoefficient_apply {ι : Type*} [Fintype ι]
    (x y : ι → E) (S : E →L[ℂ] E) :
    finiteOperatorCoefficient x y S = ∑ i, inner ℂ (y i) (S (x i)) := by
  simp [finiteOperatorCoefficient]

variable [FiniteDimensional ℂ E]

/-- The trace pairing is kept as a bounded functional so that its norm is
the ordinary dual norm, with no additional trace-class definitions. -/
def operatorTracePairing (T : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  ({ toFun S := LinearMap.trace ℂ E (T.adjoint.comp S).toLinearMap
     map_add' S R := by simp
     map_smul' c S := by simp } : (E →L[ℂ] E) →ₗ[ℂ] ℂ).toContinuousLinearMap

@[simp]
theorem operatorTracePairing_apply (T S : E →L[ℂ] E) :
    operatorTracePairing T S = LinearMap.trace ℂ E (T.adjoint.comp S).toLinearMap := rfl

theorem operatorTracePairing_rankOne (x y : E) (S : E →L[ℂ] E) :
    operatorTracePairing (rankOne ℂ x y) S = inner ℂ x (S y) := by
  rw [operatorTracePairing_apply, adjoint_rankOne]
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
  rw [← ContinuousLinearMap.toLinearMap_comp, comp_rankOne, trace_rankOne]

theorem operatorTracePairing_sum {ι : Type*} [Fintype ι]
    (T : ι → E →L[ℂ] E) (S : E →L[ℂ] E) :
    operatorTracePairing (∑ i, T i) S = ∑ i, operatorTracePairing (T i) S := by
  change LinearMap.trace ℂ E ((star (∑ i, T i) * S).toLinearMap) = _
  rw [star_sum, Finset.sum_mul, ContinuousLinearMap.toLinearMap_sum, map_sum]
  rfl

theorem exists_finite_polar_coefficients (T : E →L[ℂ] E) :
    ∃ (n : ℕ) (x y : Fin n → E),
      operatorTracePairing T = finiteOperatorCoefficient x y ∧
      (∑ i, ‖x i‖ ^ 2) ≤ ‖operatorTracePairing T‖ ∧
      (∑ i, ‖y i‖ ^ 2) ≤ ‖operatorTracePairing T‖ := by
  obtain ⟨U, hU, hUT, hUadj⟩ := exists_contractive_polar_factor T
  let R := CFC.sqrt (T.adjoint.comp T)
  have hR : R.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  obtain ⟨n, a, ha⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hR
  have hT : T = ∑ i, rankOne ℂ (U (a i)) (a i) := by
    rw [← hUT]
    change U * R = _
    rw [ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact comp_rankOne _ _ _
  have hp : operatorTracePairing T = finiteOperatorCoefficient a (fun i => U (a i)) := by
    apply ContinuousLinearMap.ext
    intro S
    rw [finiteOperatorCoefficient_apply, hT]
    simp only [operatorTracePairing_sum, operatorTracePairing_rankOne]
  have hadj : T.adjoint.comp U = R := by
    have h := congrArg ContinuousLinearMap.adjoint hUadj
    have hr : R.adjoint = R := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
    change (U.adjoint.comp T).adjoint = R.adjoint at h
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hr] at h
    exact h
  have heval : operatorTracePairing T U = (∑ i, ‖a i‖ ^ 2 : ℝ) := by
    rw [operatorTracePairing_apply, hadj, ha, ContinuousLinearMap.toLinearMap_sum, map_sum]
    simp only [trace_rankOne, inner_self_eq_norm_sq_to_K, Complex.ofReal_sum,
      Complex.ofReal_pow]
    rfl
  have hsum : (∑ i, ‖a i‖ ^ 2) ≤ ‖operatorTracePairing T‖ := by
    have h := (operatorTracePairing T).le_opNorm U
    rw [heval, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg ‖a i‖)] at h
    exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hU)
  refine ⟨n, a, (fun i => U (a i)), hp, hsum, ?_⟩
  apply le_trans (Finset.sum_le_sum fun i _ => ?_) hsum
  have hn : ‖U (a i)‖ ≤ ‖a i‖ := (U.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hU)
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem finite_dimensional_coefficient_factorization {ι : Type*} [Fintype ι]
    (x y : ι → E) :
    ∃ (n : ℕ) (a b : Fin n → E),
      finiteOperatorCoefficient x y = finiteOperatorCoefficient a b ∧
      (∑ i, ‖a i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ ∧
      (∑ i, ‖b i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ := by
  let T := ∑ i, rankOne ℂ (y i) (x i)
  have hT : operatorTracePairing T = finiteOperatorCoefficient x y := by
    ext S
    simp only [T, operatorTracePairing_sum, operatorTracePairing_rankOne,
      finiteOperatorCoefficient_apply]
  simpa only [hT] using exists_finite_polar_coefficients T

end

end KadisonKastler

end OAI
