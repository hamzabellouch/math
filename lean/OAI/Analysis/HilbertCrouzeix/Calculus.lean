import OAI.Analysis.HilbertCrouzeix.Spectrum

namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem HolomorphicOn.continuousOn {m : ℕ} {F : ℂ → Coeff m} {U : Set ℂ}
    (hF : HolomorphicOn F U) : ContinuousOn F U :=
  continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (hF i j).continuousOn

omit [CompleteSpace H] in
theorem holomorphic_max_attained [Nontrivial H] (A : H →L[ℂ] H)
    {m : ℕ} {F : ℂ → Coeff m} {U : Set ℂ}
    (hKU : numericalClosure A ⊆ U) (hF : HolomorphicOn F U) :
    IsGreatest ((fun z => ‖F z‖) '' numericalClosure A)
      (normSup (numericalClosure A) F) :=
  isGreatest_normSup (isCompact_numericalClosure A) (numericalClosure_nonempty A)
    (hF.continuousOn.mono hKU)

theorem isOpen_poleFreeSet {m : ℕ} (R : RationalMatrix m) : IsOpen (poleFreeSet R) := by
  have heq : poleFreeSet R = ⋂ i, ⋂ j, {z | (R i j).denom.eval z ≠ 0} := by
    ext z
    simp [poleFreeSet]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_ne.preimage (R i j).denom.continuous

theorem rationalFunction_holomorphic {m : ℕ} (R : RationalMatrix m) :
    HolomorphicOn (rationalFunction R) (poleFreeSet R) := by
  intro i j
  simp only [rationalFunction, RatFunc.eval, Polynomial.eval₂_id]
  exact (R i j).num.differentiable.differentiableOn.div
    (R i j).denom.differentiable.differentiableOn (fun z hz => hz i j)

omit [CompleteSpace H] in
theorem rational_max_attained [Nontrivial H] (A : H →L[ℂ] H)
    {m : ℕ} (R : RationalMatrix m) (hR : numericalClosure A ⊆ poleFreeSet R) :
    IsGreatest ((fun z => ‖rationalFunction R z‖) '' numericalClosure A)
      (normSup (numericalClosure A) (rationalFunction R)) :=
  holomorphic_max_attained A hR (rationalFunction_holomorphic R)

theorem rational_denominator_isUnit [Nontrivial H] (A : H →L[ℂ] H)
    {m : ℕ} (R : RationalMatrix m) (hR : numericalClosure A ⊆ poleFreeSet R)
    (i j : Fin m) : IsUnit (Polynomial.aeval A (R i j).denom) := by
  apply (spectrum.zero_notMem_iff ℂ).mp
  rw [spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, hz0⟩
  exact hR (spectrum_subset_numericalClosure A hz) i j hz0

section TrivialSpace
omit [CompleteSpace H]

theorem numericalRange_eq_empty [Subsingleton H] (A : H →L[ℂ] H) :
    numericalRange A = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro z ⟨x, hx, h⟩
  have hx0 : x = 0 := Subsingleton.elim _ _
  simp [hx0] at hx

theorem amplification_eq_zero [Subsingleton H] (m : ℕ) (x : Amplification H m) :
    x = 0 := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq continuous_id continuous_const) ?_
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  simp only [ha, UniformSpace.Completion.coe_zero]

theorem amplifiedOperator_eq_zero [Subsingleton H] (m : ℕ)
    (T : Amplification H m →L[ℂ] Amplification H m) : T = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact amplification_eq_zero m (T x)

end TrivialSpace

theorem zeroConclusion [Subsingleton H] (A : H →L[ℂ] H) : ZeroConclusion A := by
  have hW := numericalRange_eq_empty A
  refine ⟨hW, ?_, ?_⟩
  · intro m F
    simp [hW]
  · intro m hm
    refine ⟨amplifiedOperator_eq_zero m, ?_, ?_, ?_⟩
    · intro d B
      have hP := amplifiedOperator_eq_zero m (polynomialEval A B)
      exact ⟨hP, by simp only [hP, hW, normSup_empty, mul_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero⟩
    · intro U F
      have hF := amplifiedOperator_eq_zero m (holomorphicEval A U F)
      exact ⟨hF, by simp only [hF, hW, normSup_empty, mul_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero⟩
    · intro R
      have hR := amplifiedOperator_eq_zero m (rationalEval A R)
      exact ⟨hR, by simp only [hR, hW, normSup_empty, mul_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero⟩


end HilbertCrouzeix

end

end OAI
