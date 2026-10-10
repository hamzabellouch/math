import OAI.NumberTheory.DirichletL.Descent.Completion
import OAI.NumberTheory.DirichletL.Descent.Poisson

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
open CubicEisenstein hiding summand
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_summand_primary_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (I J : Ideal Eis) (h : summand Ψ W X I J ≠ 0) :
    primaryGenerator (I * J ^ 3) ≠ 0 := by
  have hI : primaryGenerator I ≠ 0 := by
    intro hz
    apply h
    simp [summand, columnWeight, squarefreeGaussCoefficient, hz]
  have hJ : primaryGenerator J ≠ 0 := by
    intro hz
    apply h
    rw [summand, cubeWeight_zero_of_primaryGenerator_zero Ψ J hz]
    ring
  rw [primaryGenerator_mul, show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from
    map_pow primaryGeneratorHom J 3]
  exact mul_ne_zero hI (pow_ne_zero _ hJ)

theorem markedCompletedT_congr_primary (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A, primaryGenerator A ≠ 0 → d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz : summand Ψ W X I J = 0
  · simp only [hz, zero_mul]
  · rw [h (I * J ^ 3) (completed_summand_primary_support Ψ W X I J hz)]

theorem markedCompletedT_quotient_fourier (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (F : (Eis ⧸ Ideal.span {c}) → ℂ)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => F (Ideal.Quotient.mk _ (primaryGenerator A))) =
      ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
        completedFixedFrequency Ψ c hc h W X := by
  have hinv (n : Eis) :
      F (Ideal.Quotient.mk _ n) =
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
          fixedRowFourierPhase c hc h n :=
    (finiteAdditiveFourier_inversion (quotientTrace c hc)
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) F (Ideal.Quotient.mk _ n)).symm
  have hp (p : Ideal Eis × Ideal Eis) :
      summand Ψ W X p.1 p.2 * F (Ideal.Quotient.mk _ (primaryGenerator (p.1 * p.2 ^ 3))) =
      ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
        (summand Ψ W X p.1 p.2 * fixedRowFourierPhase c hc h
          (primaryGenerator p.1 * primaryGenerator p.2 ^ 3)) := by
    rw [primaryGenerator_mul, show primaryGenerator (p.2 ^ 3) = primaryGenerator p.2 ^ 3 from
      map_pow primaryGeneratorHom p.2 3, hinv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [markedCompletedT_eq_tsum Ψ W hW X hX]
  simp_rw [hp]
  rw [Summable.tsum_finsetSum]
  · simp only [tsum_mul_left, completedFixedFrequency]
  · intro h hh
    exact (completedFixedFrequency_summable Ψ c hc h W hW X hX).mul_left _

theorem finiteAdditiveFourierCoeff_zero_delta {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (h : R) :
    finiteAdditiveFourierCoeff ψ (fun x => if x = 0 then 1 else 0) h =
      (Fintype.card R : ℂ)⁻¹ := by
  simp [finiteAdditiveFourierCoeff]

theorem markedCompletedT_divisor_fourier (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => if Ideal.span {c} ∣ A then 1 else 0) =
      (Fintype.card (Eis ⧸ Ideal.span {c}) : ℂ)⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, completedFixedFrequency Ψ c hc h W X := by
  have hmark : markedCompletedT Ψ W X (fun A => if Ideal.span {c} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        if Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator A) = 0 then 1 else 0) := by
    apply markedCompletedT_congr_primary
    intro A hA
    have hd : Ideal.span {c} ∣ A ↔
        Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator A) = 0 := by
      calc
        _ ↔ A ≤ Ideal.span {c} := Ideal.dvd_iff_le
        _ ↔ Ideal.span {primaryGenerator A} ≤ Ideal.span {c} := by
          rw [(primaryGenerator_spec A hA).1]
        _ ↔ primaryGenerator A ∈ Ideal.span {c} := Ideal.span_singleton_le_iff_mem _
        _ ↔ _ := (Ideal.Quotient.eq_zero_iff_mem).symm
    simp only [hd]
  rw [hmark, markedCompletedT_quotient_fourier c hc
    (fun x : Eis ⧸ Ideal.span {c} => if x = 0 then (1 : ℂ) else 0) Ψ W hW X hX]
  simp only [finiteAdditiveFourierCoeff_zero_delta, Finset.mul_sum]

end
end SevenEighths.InverseMoment

end OAI
