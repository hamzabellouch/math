import OAI.Probability.FreeIsing.Conditioning.CenteredCopyDifference
import OAI.Probability.FreeIsing.Spectral.NoisyLawSpectral

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.CopyDifference
open PlantedStationarity

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable (hμ : HasFreeIsingLaw theta μ) (ν : Measure A) [IsProbabilityMeasure ν]
variable {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
variable {π : Measure ((TreeVertex d → B) × (TreeVertex d → B))}
variable (hp : MeasurePreserving Prod.fst π (NoisyLawSpectral.law μ ν O))
variable (hq : MeasurePreserving Prod.snd π (NoisyLawSpectral.law μ ν O))
variable (hπ : ∀ g : TreeAut d, MeasurePreserving
  (Prod.map (relabel g) (relabel g)) π π)

def noisyAverageOnDifferences :
    rangeClosure (operator hp hq) →L[ℝ] rangeClosure (operator hp hq) :=
  averageOnDifferences hp hq (TreeLawKoopman.reflection (A := B))
    (fun c => Prod.map (relabel (prefixTreeAut c)) (relabel (prefixTreeAut c)))
    (fun c => measurePreserving_coordinateMap_relabel hμ ν O hO (prefixTreeAut c))
    (fun c => hπ (prefixTreeAut c)) (fun _ => rfl) (fun _ => rfl)

omit [MeasurableSpace B] in
private theorem diagonalReflection_involutive (c : Fin d) :
    Function.Involutive
      (Prod.map (TreeLawKoopman.reflection (A := B) c)
        (TreeLawKoopman.reflection (A := B) c)) := by
  intro p
  exact Prod.ext (TreeLawKoopman.reflection_involutive c p.1)
    (TreeLawKoopman.reflection_involutive c p.2)

theorem noisyAverageOnDifferences_isSelfAdjoint :
    IsSelfAdjoint (noisyAverageOnDifferences hμ ν hO hp hq hπ) :=
  averageOnDifferences_isSelfAdjoint hp hq _ _ _ _ diagonalReflection_involutive
    (fun _ => rfl) (fun _ => rfl)

theorem noisyAverageOnDifferences_norm_le (hd : 3 ≤ d)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    ‖noisyAverageOnDifferences hμ ν hO hp hq hπ‖ ≤
      2 * Real.sqrt ((d : ℝ) - 1) / d := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure (NoisyLawSpectral.law μ ν O) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_coordinateMap hO).aemeasurable).mpr inferInstance
  apply norm_averageOnDifferences_le hp hq _ _ _ _
    TreeLawKoopman.reflection_involutive diagonalReflection_involutive
    (fun _ => rfl) (fun _ => rfl)
  · positivity
  · exact NoisyLawSpectral.centeredAverage_norm_le_critical hμ hd h0 h1 hthreshold ν hO

end Problem367.CopyDifference

end

end OAI
