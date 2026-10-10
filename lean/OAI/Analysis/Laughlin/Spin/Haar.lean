import Mathlib.MeasureTheory.Measure.Haar.Basic
import OAI.Analysis.Laughlin.Spin.Compact
import OAI.Analysis.Laughlin.Spin.CompactAverage

namespace OAI

namespace Laughlin.Rotation
open MeasureTheory MeasureTheory.Measure TopologicalSpace

noncomputable instance sourceSU2_measurableSpace : MeasurableSpace SourceSU2 := borel SourceSU2
instance sourceSU2_borelSpace : BorelSpace SourceSU2 := ⟨rfl⟩

noncomputable def sourceHaar : Measure SourceSU2 :=
  haarMeasure (⊤ : PositiveCompacts SourceSU2)

instance sourceHaar_isHaar : IsHaarMeasure sourceHaar :=
  inferInstanceAs (IsHaarMeasure (haarMeasure (⊤ : PositiveCompacts SourceSU2)))

instance sourceHaar_isProbability : IsProbabilityMeasure sourceHaar where
  measure_univ := by
    simpa [sourceHaar] using (haarMeasure_self (K₀ := (⊤ : PositiveCompacts SourceSU2)))

theorem sourceHaar_univ : sourceHaar Set.univ=1 := measure_univ

theorem source_tensor_haar_average_commutes (Q : ℕ)
    (M : Matrix (Fin Q → Fin 2) (Fin Q → Fin 2) ℂ) (g : SourceSU2) :
    sourceTensorRepresentation Q g * matrixIntegral sourceHaar (conjugateOrbit (sourceTensorRepresentation Q) M) =
      matrixIntegral sourceHaar (conjugateOrbit (sourceTensorRepresentation Q) M) * sourceTensorRepresentation Q g := by
  exact compact_haar_average_commutes sourceHaar (sourceTensorRepresentation Q)
    (sourceTensorRepresentation_continuous Q) M g

theorem source_tensor_haar_average_trace (Q : ℕ)
    (M : Matrix (Fin Q → Fin 2) (Fin Q → Fin 2) ℂ) :
    Matrix.trace (matrixIntegral sourceHaar (conjugateOrbit (sourceTensorRepresentation Q) M)) = Matrix.trace M := by
  exact compact_haar_average_trace sourceHaar (sourceTensorRepresentation Q)
    (sourceTensorRepresentation_continuous Q) M

end Laughlin.Rotation

end OAI
