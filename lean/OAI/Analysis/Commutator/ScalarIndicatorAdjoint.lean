import Mathlib
import OAI.Analysis.Commutator.ScalarIndicator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma indicatorOperator_selfAdjoint (s : Set Ω) (hs : MeasurableSet s) :
    IsSelfAdjoint (indicatorOperator (H:=H) μ s hs) := by
  classical
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorOperator_ae μ s hs f,indicatorOperator_ae μ s hs g]
    with a hf hg
  rw [hf,hg]
  by_cases ha : a∈s <;> simp [ha]

end Kadison.Decomposable

end

end
end

end OAI
