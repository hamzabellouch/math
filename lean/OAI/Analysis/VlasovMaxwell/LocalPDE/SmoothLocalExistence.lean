import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SlabEvolutionRegularity

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma C1ClassicalPrefix.toSmooth {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T)
    (hf : ContDiffOn ℝ ∞ s.f (particleSlab T))
    (hE : ContDiffOn ℝ ∞ s.E (fieldSlab T)) (hB : ContDiffOn ℝ ∞ s.B (fieldSlab T)) :
    SmoothClassicalPrefix d s T :=
  ⟨hf,hE,hB,hs.nonnegative,hs.E_L2,hs.B_L2,hs.compact,hs.equations,
    hs.initial_f,hs.initial_E,hs.initial_B⟩

theorem exists_local_smooth_prefix (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, SmoothClassicalPrefix d s T ∧ SlabEquations s T := by
  obtain ⟨T,hT,s,hs,heq,hf,hE,hB⟩ := exists_local_smooth_classical_prefix d hd
  exact ⟨T,hT,s,hs.toSmooth hf hE hB,heq⟩

end RVM

end

end OAI
