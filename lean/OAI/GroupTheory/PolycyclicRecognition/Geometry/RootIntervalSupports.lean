import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSampling

namespace OAI

/-! # Compact supports of the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Metric

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L]
  [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N]

/-- The closed interval image carries the complete sampling law. -/
def rootIntervalSupport (Exp : L → N) {m : ℕ} (letters : Fin m → I)
    (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) : Set N :=
  rootIntervalSample Exp letters X s r j '' closedBall 0 R

omit [MeasurableSpace N] [BorelSpace N] [T2Space N] in
theorem isCompact_rootIntervalSupport (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) :
    IsCompact (rootIntervalSupport Exp letters X s r R j) :=
  (isCompact_closedBall (0 : ℝ) R).image (hcont _)

theorem rootIntervalLaw_ae_mem_support (Exp : L → N)
    (hcont : ∀ v : L, Continuous (fun t : ℝ => Exp (t • v)))
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ) (r R : ℝ) (j : ℕ) :
    ∀ᵐ u ∂rootIntervalLaw Exp letters X s r R j,
      u ∈ rootIntervalSupport Exp letters X s r R j := by
  apply (ae_map_iff (hcont _).measurable.aemeasurable
    (isCompact_rootIntervalSupport Exp hcont letters X s r R j).measurableSet).mpr
  exact (ProbabilityTheory.ae_cond_mem measurableSet_closedBall).mono
    (fun t ht => mem_image_of_mem _ ht)

end PolycyclicRecognition

end

end OAI
