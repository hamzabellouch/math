import OAI.Analysis.KadisonKastler.BilateralRandomWalk

namespace OAI

/-! # The two boundary endpoints of a bilateral random walk

The forward and reflected backward halves have the exact boundary product
law. Every integer shift preserves the bilateral path probability.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory ProbabilityTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def bilateralPositiveBoundary (ω : BilateralWalkPath G) : RandomWalkBoundary G :=
  randomWalkIdentityBoundary G (bilateralFuture G ω)

def bilateralNegativeBoundary (ω : BilateralWalkPath G) : RandomWalkBoundary G :=
  randomWalkIdentityBoundary G (bilateralReflectedPast G ω)

theorem bilateralPositiveBoundary_measurePreserving :
    MeasurePreserving (bilateralPositiveBoundary G) (bilateralWalkLaw G) (randomWalkBoundaryMeasure G) :=
  (randomWalkIdentityBoundary_measurePreserving G).comp
    ⟨bilateralFuture_measurable G, bilateralFuture_law G⟩

theorem bilateralNegativeBoundary_measurePreserving :
    MeasurePreserving (bilateralNegativeBoundary G) (bilateralWalkLaw G) (randomWalkBoundaryMeasure G) :=
  (randomWalkIdentityBoundary_measurePreserving G).comp
    ⟨bilateralReflectedPast_measurable G, bilateralReflectedPast_law G⟩

theorem bilateralBoundary_independent :
    IndepFun (bilateralPositiveBoundary G) (bilateralNegativeBoundary G) (bilateralWalkLaw G) :=
  (bilateral_reflected_halves_independent G).comp
    (randomWalkIdentityBoundary_measurePreserving G).measurable
    (randomWalkIdentityBoundary_measurePreserving G).measurable

def bilateralBoundaryPair (ω : BilateralWalkPath G) : RandomWalkBoundary G × RandomWalkBoundary G :=
  (bilateralPositiveBoundary G ω, bilateralNegativeBoundary G ω)

theorem bilateralBoundaryPair_measurePreserving :
    MeasurePreserving (bilateralBoundaryPair G) (bilateralWalkLaw G)
      ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G)) := by
  have hp := bilateralPositiveBoundary_measurePreserving G
  have hn := bilateralNegativeBoundary_measurePreserving G
  refine ⟨hp.measurable.prodMk hn.measurable, ?_⟩
  exact ((bilateralBoundary_independent G).map_prod_eq_prod_map_map hp.measurable.aemeasurable
    hn.measurable.aemeasurable).trans (by rw [hp.map_eq, hn.map_eq])

def bilateralTranslate (k : ℤ) (ω : BilateralWalkPath G) (j : ℤ) : G := ω (j + k)

theorem bilateralTranslate_measurePreserving (k : ℤ) :
    MeasurePreserving (bilateralTranslate G k) (bilateralWalkLaw G) (bilateralWalkLaw G) := by
  refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (j + k)), ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => add_right_cancel h)

end

end KadisonKastler

end OAI
