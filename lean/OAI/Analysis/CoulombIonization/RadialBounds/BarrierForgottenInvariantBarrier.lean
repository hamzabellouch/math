import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierInitialLipschitzBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma DeterministicLocalBound.comp {Ω D : Type*} {u : D → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (X : Ω → D) : DeterministicLocalBound (fun sample => u (X sample)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  exact ⟨C,fun sample x hx => hC (X sample) x hx⟩

lemma DeterministicLocalLipschitz.comp {Ω D : Type*} {u : D → TFSpace → ℝ}
    (hu : DeterministicLocalLipschitz u) (X : Ω → D) : DeterministicLocalLipschitz (fun sample => u (X sample)) := by
  intro x
  obtain ⟨K,s,hs,hK⟩ := hu x
  exact ⟨K,s,hs,fun sample => hK (X sample)⟩

end CoulombBarrier

end

end OAI
