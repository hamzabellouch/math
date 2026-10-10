import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixExchangeRegions
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixWindows

namespace OAI

/-! # Uniform time bounds for compact physical rectangles -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

theorem compact_subset_remainingWindow (c : EliminationChain P D)
    (K : Set c.Time) (hK : IsCompact K) (R : ℝ) :
    ∃ m : ℕ, K ⊆ c.remainingWindow R m := by
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover (c.remainingWindow R)
    (c.remainingWindow_open R) (by rw [c.remainingWindow_cover]; exact subset_univ K)
  refine ⟨F.sup id,?_⟩
  intro x hx
  obtain ⟨m,hm⟩ := mem_iUnion.mp (hF hx)
  obtain ⟨hmF,hxm⟩ := mem_iUnion.mp hm
  exact c.remainingWindow_mono R (Finset.le_sup hmF) hxm

end EliminationChain
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

lemma continuous_nextTimeConjugation : Continuous
    (fun z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root) =>
      nextTimeCoordinates q c hf (q.nextConjugation d z.1 z.2)) :=
  (nextTimeCoordinates q c hf).continuous.comp (q.continuous_conjugationSkew d).snd

theorem compact_nextTimeConjugation_bound
    (K : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hK : IsCompact K)
    (I : Set ℝ) (hI : IsCompact I) :
    ∃ m : ℕ, ∀ w ∈ K, ∀ t ∈ I,
      nextTimeCoordinates q c hf (q.nextConjugation d t w) ∈ c.remainingWindow 1 m := by
  let F := fun z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root) =>
    nextTimeCoordinates q c hf (q.nextConjugation d z.1 z.2)
  obtain ⟨m,hm⟩ := c.compact_subset_remainingWindow (F '' (I ×ˢ K))
    ((hI.prod hK).image (continuous_nextTimeConjugation q c hf)) 1
  exact ⟨m,fun w hw t ht => hm ⟨(t,w),⟨ht,hw⟩,rfl⟩⟩

variable {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

theorem exchangedRectangleRegion_time_bounded
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) (J : Set ℝ)
    (K : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hK : IsCompact K)
    (hQK : Q.second ⊆ K) (I : Set ℝ) (hI : IsCompact I) (hJI : J ⊆ I) :
    ∃ m : ℕ, ∀ z ∈ C.exchangedRectangleRegion q g k c hf Q J,
      z.2 ∈ c.remainingWindow 1 m := by
  obtain ⟨m,hm⟩ := compact_nextTimeConjugation_bound q c hf K hK I hI
  refine ⟨m,?_⟩
  rintro z ⟨w,hw,rfl⟩
  exact hm w.2.1.val (hQK w.2.1.prop) w.2.2 (hJI hw.2.2)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
