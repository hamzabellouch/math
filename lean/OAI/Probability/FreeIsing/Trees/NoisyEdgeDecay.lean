import OAI.Probability.FreeIsing.Conditioning.NoisyCopyDifference
import OAI.Probability.FreeIsing.Spectral.DifferenceKoopman
import OAI.Probability.FreeIsing.Trees.ColoredEdgeDecay

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.CopyDifference
open PlantedStationarity ColoredEdgeLifts

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable (hμ : HasFreeIsingLaw theta μ) (ν : Measure A) [IsProbabilityMeasure ν]
variable {O : IsingSpin → A → B} (hO : Measurable (Function.uncurry O))
variable {π : Measure ((TreeVertex d → B) × (TreeVertex d → B))}
variable (hp : MeasurePreserving Prod.fst π (NoisyLawSpectral.law μ ν O))
variable (hq : MeasurePreserving Prod.snd π (NoisyLawSpectral.law μ ν O))
variable (hπ : ∀ g : TreeAut d, MeasurePreserving
  (Prod.map (relabel g) (relabel g)) π π)

omit [MeasurableSpace B] in
private theorem pairReflection_involutive (c : Fin d) :
    Function.Involutive
      (Prod.map (TreeLawKoopman.reflection (A := B) c)
        (TreeLawKoopman.reflection (A := B) c)) := by
  intro p
  exact Prod.ext (TreeLawKoopman.reflection_involutive c p.1)
    (TreeLawKoopman.reflection_involutive c p.2)

def noisyDifferenceReflection (c : Fin d) :
    rangeClosure (operator hp hq) ≃ₗᵢ[ℝ] rangeClosure (operator hp hq) :=
  differenceKoopmanEquiv hp hq (TreeLawKoopman.reflection c)
    (Prod.map (relabel (prefixTreeAut c)) (relabel (prefixTreeAut c)))
    (measurePreserving_coordinateMap_relabel hμ ν O hO (prefixTreeAut c))
    (hπ (prefixTreeAut c)) rfl rfl (pairReflection_involutive c)

theorem noisyDifferenceReflection_involutive (c : Fin d) :
    Function.Involutive (noisyDifferenceReflection hμ ν hO hp hq hπ c) :=
  differenceKoopmanEquiv_involutive hp hq _ _ _ _ rfl rfl
    (pairReflection_involutive c)

theorem neighborAverage_noisyDifferenceReflection :
    neighborAverage (noisyDifferenceReflection hμ ν hO hp hq hπ) =
      noisyAverageOnDifferences hμ ν hO hp hq hπ := by
  exact neighborAverage_differenceKoopmanEquiv hp hq _ _ _ _ _ _ _

theorem noisy_forwardOperator_pow_bound (hd : 3 ≤ d)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖forwardOperator (by omega : 0 < d)
        (noisyDifferenceReflection hμ ν hO hp hq hπ) ((d : ℝ) - 1)⁻¹ ^ n‖ ≤
        K * ((n : ℝ) + 1) * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n := by
  apply exists_forwardOperator_pow_bound hd _
    (noisyDifferenceReflection_involutive hμ ν hO hp hq hπ)
  rw [neighborAverage_noisyDifferenceReflection]
  exact noisyAverageOnDifferences_norm_le hμ ν hO hp hq hπ hd h0 h1 hthreshold

theorem summable_noisy_forwardOperator_pow (hd : 3 ≤ d)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hthreshold : theta ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹) :
    Summable (fun n : ℕ => ‖forwardOperator (by omega : 0 < d)
      (noisyDifferenceReflection hμ ν hO hp hq hπ) ((d : ℝ) - 1)⁻¹ ^ n‖) := by
  apply summable_norm_forwardOperator_pow hd _
    (noisyDifferenceReflection_involutive hμ ν hO hp hq hπ)
  rw [neighborAverage_noisyDifferenceReflection]
  exact noisyAverageOnDifferences_norm_le hμ ν hO hp hq hπ hd h0 h1 hthreshold

end Problem367.CopyDifference

end

end OAI
