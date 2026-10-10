import OAI.Analysis.CircleDomains.Topology.AffinePathTime
import OAI.Analysis.CircleDomains.Probability.ExitTimeMeasurability

namespace OAI

/-! Measurable reparametrization of the path after its last collar hit. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def terminalPath (γ : C(PathTime, X)) (a : PathTime) : C(PathTime, X) :=
  γ.comp (affinePathTime a ⊤)

theorem continuous_terminalPath :
    Continuous (fun p : C(PathTime, X) × PathTime => terminalPath p.1 p.2) := by
  have ht : Continuous (fun p : PathTime × PathTime => affinePathTime p.1 ⊤ p.2) := by
    apply Continuous.subtype_mk
    change Continuous (fun p : PathTime × PathTime =>
      (1 - (p.2 : ℝ)) * (p.1 : ℝ) + (p.2 : ℝ) * 1)
    fun_prop
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    (ht.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_lastEntryPath (V : Set X) (hV : IsOpen V) :
    Measurable (fun γ : C(PathTime, X) => terminalPath γ (lastEntryTime γ V)) :=
  continuous_terminalPath.measurable.comp (measurable_id.prodMk (measurable_lastEntryTime V hV))

end CircleDomainRigidity

end

end OAI
