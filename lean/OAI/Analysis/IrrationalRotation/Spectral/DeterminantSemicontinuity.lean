import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Model.VectorTraceState
import OAI.Analysis.IrrationalRotation.Spectral.SpectralNaturality

namespace OAI

noncomputable section

open scoped ENNReal CStarAlgebra

namespace Invariant233

section CStar

variable {A : Type*} [CStarAlgebra A]

theorem continuous_regularizedLog (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun a : A => CFC.log (star a * a + ε • (1 : A))) := by
  apply CFC.continuousOn_log.comp_continuous
    ((continuous_id.star.mul continuous_id).add continuous_const)
  intro a
  refine ⟨?_, ?_⟩
  · simp [IsSelfAdjoint]
  · apply (spectrum.zero_notMem_iff ℝ).mp
    intro hz
    exact (lt_irrefl (0 : ℝ)) (regularizedNormSquare_spectrum_pos a ε hε 0 hz)

theorem upperSemicontinuous_fugledeKadisonDeterminant (τ : TracialState A) :
    UpperSemicontinuous (fugledeKadisonDeterminant τ) := by
  apply upperSemicontinuous_iInf
  intro ε
  apply Continuous.upperSemicontinuous
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (((Complex.continuous_re.comp τ.toContinuousLinearMap.continuous).comp
      (continuous_regularizedLog ε.val ε.property)).div_const 2))

theorem isOpen_fugledeKadisonDeterminant_lt (τ : TracialState A) (r : ℝ≥0∞) :
    IsOpen {a : A | fugledeKadisonDeterminant τ a < r} :=
  (upperSemicontinuous_fugledeKadisonDeterminant τ).isOpen_preimage r

theorem continuousAt_fugledeKadisonDeterminant_of_eq_zero
    (τ : TracialState A) {a : A} (ha : fugledeKadisonDeterminant τ a = 0) :
    ContinuousAt (fugledeKadisonDeterminant τ) a := by
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨?_, upperSemicontinuous_fugledeKadisonDeterminant τ a⟩
  intro r hr
  rw [ha] at hr
  exact (not_lt_of_ge bot_le hr).elim

end CStar

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem upperSemicontinuous_vectorFugledeKadisonDeterminant (ξ : H) :
    UpperSemicontinuous (vectorFugledeKadisonDeterminant ξ) := by
  apply upperSemicontinuous_iInf
  intro ε
  apply Continuous.upperSemicontinuous
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (((Complex.continuous_re.comp (vectorTraceCLM ξ).continuous).comp
      (continuous_regularizedLog ε.val ε.property)).div_const 2))

theorem isOpen_vectorFugledeKadisonDeterminant_lt (ξ : H) (r : ℝ≥0∞) :
    IsOpen {T : H →L[ℂ] H | vectorFugledeKadisonDeterminant ξ T < r} :=
  (upperSemicontinuous_vectorFugledeKadisonDeterminant ξ).isOpen_preimage r

theorem continuousAt_vectorFugledeKadisonDeterminant_of_eq_zero
    (ξ : H) {T : H →L[ℂ] H} (hT : vectorFugledeKadisonDeterminant ξ T = 0) :
    ContinuousAt (vectorFugledeKadisonDeterminant ξ) T := by
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨?_, upperSemicontinuous_vectorFugledeKadisonDeterminant ξ T⟩
  intro r hr
  rw [hT] at hr
  exact (not_lt_of_ge bot_le hr).elim

end Vector

end Invariant233

end

end OAI
