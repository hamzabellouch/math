import OAI.Probability.ClassicalON.ThetaEstimates

namespace OAI

universe uE uI uJ uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype V] [Fintype E] [Fintype I] in
theorem coefficientObservable_norm_le (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E) (σ : V → Spin 3) :
    ‖S.coefficientObservable M e σ‖ ≤ β := by
  change ‖(S.localCoefficient M σ e : ℂ)‖ ≤ β
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact S.abs_localCoefficient_le β hb M hM σ e

omit [Fintype I] in
theorem averageComplex_pos_square (S : SpinSystem 3 V E) (F : C((V → Spin 3), ℂ)) :
    0 ≤ (S.averageComplexLinear (F * conjugateObservable F)).re := by
  rw [S.averageComplex_re]
  apply S.averageLinear_nonneg
  intro σ
  change 0 ≤ (F σ * conj (F σ)).re
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

omit [Fintype I] in
theorem norm_averageComplex_sum_le {J : Type uJ} [Fintype J]
    (S : SpinSystem 3 V E) (F : J → C((V → Spin 3), ℂ)) (bound : J → ℝ)
    (hF : ∀ j, ‖S.averageComplexLinear (F j)‖ ≤ bound j) :
    ‖S.averageComplexLinear (∑ j, F j)‖ ≤ ∑ j, bound j := by
  rw [map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hF j)

def familyPaired (S : SpinSystem 3 V E) (u : I → E → ℂ) : C((V → Spin 3), ℂ) :=
  ∑ i, (S.currentObservable axisA (u i) *
    S.currentObservable axisB (fun e => conj (u i e)) +
    S.currentObservable mixedAB (fun e => u i e * conj (u i e)))

def familyRemainder (S : SpinSystem 3 V E) (u : I → E → ℂ) : C((V → Spin 3), ℂ) :=
  let T := familyKernel u
  let X := fun M e => S.currentObservable M (T e)
  let C := S.coefficientObservable
  let bar := conjugateObservable
  let k := fun z => ContinuousMap.const (V → Spin 3) z
  (∑ e, C (axisA^2) e * X axisB e * bar (X axisB e)) +
  (∑ e, C mixedAB e * X axisB e * X axisA e) +
  (∑ e, C mixedAB e * bar (X axisA e) * bar (X axisB e)) +
  (∑ e, C (axisB^2) e * bar (X axisA e) * X axisA e) +
  (∑ e, ∑ l, C (axisA^2) e * C (axisB^2) l * k (T e l * conj (T e l))) +
  (∑ e, ∑ l, C mixedAB e * C mixedAB l * k (T e l ^ 2)) +
  (∑ e, C mixedAAB e * k (T e e) * bar (X axisB e)) +
  (∑ e, C mixedABB e * k (T e e) * X axisA e) +
  (∑ e, C mixedAAB e * k (conj (T e e)) * X axisB e) +
  (∑ e, C mixedABB e * k (conj (T e e)) * bar (X axisA e)) +
  (∑ e, C mixedAABB e * k (T e e * conj (T e e)))

omit [Fintype V] in

theorem familyObservable_contraction (S : SpinSystem 3 V E) (u : I → E → ℂ) :
    (∑ i, ∑ j, S.complexMixedObservable (u i) (fun e => conj (u i e))
      (fun e => conj (u j e)) (u j)) =
        S.familyPaired u * conjugateObservable (S.familyPaired u) + S.familyRemainder u := by
  ext σ
  have h := MixedAlgebra.four_family_contraction (S.complexCoefficients σ) u
    (fun i e => conj (u i e)) (fun i e => conj (u i e)) u
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    complexMixedObservable, ContinuousMap.coe_mk]
  rw [h]
  simp only [familyPaired, familyRemainder, ContinuousMap.sum_apply,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, conjugateObservable_apply,
    ContinuousMap.const_apply, currentObservable, coefficientObservable,
    ContinuousMap.coe_mk, MixedAlgebra.paired, MixedAlgebra.kernel,
    familyKernel, complexCoefficients, MixedAlgebra.Coeffs.map,
    mixedCoefficients, Function.comp_def, Complex.ofRealHom_eq_coe,
    complexEnergy, map_sum, map_add, map_mul,
    starRingEnd_self_apply, pow_two]
  congr 1
  all_goals simp only [MixedAlgebra.weighted, MixedAlgebra.kernel, familyKernel,
    map_sum, map_mul, Complex.conj_ofReal, starRingEnd_self_apply, Pi.mul_apply, mul_assoc]

end ClassicalON.SpinSystem

end

end OAI
