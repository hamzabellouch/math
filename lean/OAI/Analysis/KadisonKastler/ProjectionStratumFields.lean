import OAI.Analysis.KadisonKastler.ProjectionStrataCoordinates

namespace OAI

/-! # Transporting actual operator fields to the fixed-coordinate strata -/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

def compressedStratumField (R : X → H →L[ℂ] H) (n : ℕ)
    (x : projectionRankStratum P b n) :
    ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ) :=
  (projectionStratumAnalysis P hP b hb n x).comp
    ((R x.val).comp (projectionStratumSynthesis P hP b hb n x).toContinuousLinearMap)

theorem compressedStratumField_norm_le (hPn : ∀ x, ‖P x‖ ≤ 1)
    (R : X → H →L[ℂ] H) (n : ℕ) (x : projectionRankStratum P b n) :
    ‖compressedStratumField P hP b hb R n x‖ ≤ ‖R x.val‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖projectionStratumAnalysis P hP b hb n x
    (R x.val (projectionStratumSynthesis P hP b hb n x v))‖ ≤ _
  calc
    _ ≤ ‖P x.val‖ * ‖R x.val (projectionStratumSynthesis P hP b hb n x v)‖ :=
      projectionStratumAnalysis_apply_norm_le P hP b hb n x _
    _ ≤ ‖R x.val (projectionStratumSynthesis P hP b hb n x v)‖ :=
      (mul_le_mul_of_nonneg_right (hPn x.val) (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ‖R x.val‖ * ‖projectionStratumSynthesis P hP b hb n x v‖ := (R x.val).le_opNorm _
    _ = _ := by rw [LinearIsometry.norm_map]

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

local instance compressedCoordinateMeasurable (n : ℕ) : MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  borel _
local instance compressedCoordinateBorel (n : ℕ) : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩
local instance compressedCoordinateSeparable (n : ℕ) :
    TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  separable_scalarHilbertCoordinates

theorem compressedStratumField_aestronglyMeasurable
    (hPm : ∀ v, Measurable fun x => P x v) (R : X → H →L[ℂ] H) (n : ℕ)
    (μ : Measure (projectionRankStratum P b n))
    (hR : ∀ v, AEStronglyMeasurable (fun x => R x.val v) μ)
    (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    AEStronglyMeasurable (fun x => compressedStratumField P hP b hb R n x v) μ :=
  aestronglyMeasurable_linearField_apply μ (projectionStratumAnalysis P hP b hb n)
    (fun z => (projectionStratumAnalysis_measurable P hP b hb hPm n z).aestronglyMeasurable)
    _ (aestronglyMeasurable_linearField_apply μ (fun x => R x.val) hR _
      ((projectionStratumSynthesis_measurable P hP b hb hPm n v).aestronglyMeasurable))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) (hPm : ∀ v, Measurable fun x => P x v) (hPn : ∀ x, ‖P x‖ ≤ 1)
  (J : E →ₗᵢ[ℂ] Lp H 2 μ)
  (hJ : ∀ f : Lp H 2 μ, KadisonSimilarity.isometricExtension J 1 f =ᵐ[μ]
    fun x => P x (f x))

theorem projectionStrataCoordinates_operator_action
    (T : E →L[ℂ] E) (R : X → H →L[ℂ] H)
    (hRT : ∀ v : E, J (T v) =ᵐ[μ] fun x => R x (J v x)) (v : E) (n : ℕ) :
    ∀ᵐ x : projectionRankStratum P b n ∂projectionStratumMeasure μ P b n,
      projectionStrataCoordinates μ P hP b hb hPm hPn J hJ (T v) n x =
        compressedStratumField P hP b hb R n x
          (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x) := by
  have hr := (ae_restrict_iff_subtype (measurableSet_projectionRankStratum P b hPm n)).mp
    (ae_restrict_of_ae (hRT v))
  filter_upwards [projectionStrataCoordinates_fiber_ae μ P hP b hb hPm hPn J hJ (T v) n,
    projectionStrataCoordinates_fiber_ae μ P hP b hb hPm hPn J hJ v n, hr] with x ht hv hr
  let A := projectionStratumAnalysis P hP b hb n x
  calc
    _ = A (projectionStratumSynthesis P hP b hb n x
        (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ (T v) n x)) :=
      (projectionStratumAnalysis_synthesis P hP b hb n x _).symm
    _ = A (J (T v) x.val) := congrArg A ht
    _ = A (R x.val (J v x.val)) := congrArg A hr
    _ = A (R x.val (projectionStratumSynthesis P hP b hb n x
        (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x))) :=
      congrArg (fun z => A (R x.val z)) hv.symm
    _ = _ := rfl

end

end KadisonKastler

end OAI
