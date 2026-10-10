import OAI.Analysis.KadisonKastler.ShiftBoundarySpace

namespace OAI

/-! # The boundary law of a walk starting at the identity

The initial root law was chosen with full support. Starting at the identity
is absolutely continuous before taking the invariant factor; after one
increment its boundary law is exactly the chosen boundary probability.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkFromIdentity (ω : ℕ → G) : RandomWalkPath G := (1, ω)

omit [Countable G] [MeasurableSingletonClass G] in
theorem randomWalkFromIdentity_measurable : Measurable (randomWalkFromIdentity G) :=
  measurable_const.prodMk measurable_id

theorem randomWalkFromIdentity_quasi :
    Measure.QuasiMeasurePreserving (randomWalkFromIdentity G)
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) (randomWalkPathLaw G) := by
  refine ⟨randomWalkFromIdentity_measurable G, ?_⟩
  change (Measure.map (Prod.mk (1 : G)) (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))) ≪ _
  rw [← Measure.dirac_prod]
  exact Measure.AbsolutelyContinuous.prod
    (absolutelyContinuous_symmetricRandomWalkLaw (Measure.dirac 1))
    (Measure.AbsolutelyContinuous.refl _)

theorem randomWalkAdvance_fromIdentity_law :
    (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)).map
      (randomWalkAdvance G ∘ randomWalkFromIdentity G) = randomWalkPathLaw G := by
  simpa [Function.comp_def, randomWalkAdvance, randomWalkFromIdentity, randomWalkPathLaw] using
    iid_first_increment_tail_law (symmetricRandomWalkLaw G)

def randomWalkIdentityBoundary (ω : ℕ → G) : RandomWalkBoundary G :=
  shiftBoundaryMap (randomWalkPathLaw G) (randomWalkAdvance G) (randomWalkFromIdentity G ω)

theorem randomWalkIdentityBoundary_measurePreserving :
    MeasurePreserving (randomWalkIdentityBoundary G)
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) (randomWalkBoundaryMeasure G) := by
  have hm : Measurable (randomWalkIdentityBoundary G) :=
    (shiftBoundaryMap_measurePreserving (randomWalkPathLaw G) (randomWalkAdvance G)).measurable.comp
      (randomWalkFromIdentity_measurable G)
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro A hA
  change MeasurableSet[shiftInvariantSigma (randomWalkPathLaw G) (randomWalkAdvance G)] A at hA
  rw [Measure.map_apply hm hA]
  change _ = (randomWalkPathLaw G).trim (shiftInvariantSigma_le _ _) A
  rw [trim_measurableSet_eq _ hA, ← randomWalkAdvance_fromIdentity_law G,
    Measure.map_apply ((randomWalkAdvance_measurable G).comp (randomWalkFromIdentity_measurable G)) hA.1]
  apply measure_congr
  have hs := (randomWalkFromIdentity_quasi G).ae hA.2
  filter_upwards [hs] with ω hω
  exact propext hω.symm

end

end KadisonKastler

end OAI
