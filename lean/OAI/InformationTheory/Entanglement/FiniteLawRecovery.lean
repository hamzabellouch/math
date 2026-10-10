import OAI.InformationTheory.Entanglement.MatrixMeasureChannel
import OAI.InformationTheory.Entanglement.InstrumentCovariance

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {n e : Type} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]

theorem finite_branch_law_recovery (i₀ : n) (B : Matrix e n ℂ) :
    ∃ F : Map e n, ∃ hF : CP F, TracePreserving F ∧
      ∀ W : PositiveMatrixMeasure T n,
        (W.filter B).channel F hF=W.filter (CFC.sqrt (Bᴴ*B)) := by
  obtain ⟨F,hF,hT,hrec⟩ := finite_purification_recovery i₀ B
  refine ⟨F,hF,hT,?_⟩
  intro W
  apply PositiveMatrixMeasure.eq_of_value
  intro s hs
  rw [PositiveMatrixMeasure.channel_value,PositiveMatrixMeasure.filter_value,
    PositiveMatrixMeasure.filter_value]
  simpa only [(sqrt_psd (Bᴴ*B)).isHermitian.eq] using hrec (W.value s)

theorem finite_purification_distance_recovery (i₀ : n) (B : Matrix e n ℂ) :
    ∃ F : Map e n, ∃ hF : CP F, TracePreserving F ∧
      ∀ (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n) (σ : PositiveMatrixMeasure T e),
        cqBitDistance (fun i j => (W i j).filter (CFC.sqrt (Bᴴ*B))) (σ.channel F hF)≤
          cqBitDistance (fun i j => (W i j).filter B) σ := by
  obtain ⟨F,hF,hT,hrec⟩ := finite_branch_law_recovery (T := T) i₀ B
  refine ⟨F,hF,hT,?_⟩
  intro W σ
  have h := cqBitDistance_channel (fun i j => (W i j).filter B) σ F hF hT
  simpa only [hrec] using h

end SecretKey

end

end OAI
