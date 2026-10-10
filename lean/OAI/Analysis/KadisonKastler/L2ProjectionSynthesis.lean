import OAI.Analysis.KadisonKastler.L2LinearFields
import OAI.Analysis.KadisonKastler.ProjectionDimensionStrata

namespace OAI

/-! # L² synthesis on a projection-rank stratum

The measurable orthonormal coordinates provide actual isometric inclusions
from the fixed-coordinate L² spaces into the original coefficient space.
-/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

def projectionStratumSynthesis (n : ℕ) (x : projectionRankStratum P b n) :
    ℓ²(projectionDimensionIndex n, ℂ) →ₗᵢ[ℂ] H :=
  (P x.val).range.subtypeₗᵢ.comp
    (projectionStratumCoordinates P hP b hb n x).symm.toLinearIsometry

def projectionStratumAnalysis (n : ℕ) (x : projectionRankStratum P b n) :
    H →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ) :=
  (projectionStratumCoordinates P hP b hb n x).toLinearIsometry.toContinuousLinearMap.comp
    (P x.val).rangeRestrict

theorem projectionStratumSynthesis_analysis (n : ℕ)
    (x : projectionRankStratum P b n) (v : H) :
    projectionStratumSynthesis P hP b hb n x
      (projectionStratumAnalysis P hP b hb n x v) = P x.val v := by
  change ((projectionStratumCoordinates P hP b hb n x).symm
    ((projectionStratumCoordinates P hP b hb n x) ⟨P x.val v, ⟨v, rfl⟩⟩) : H) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem projectionStratumSynthesis_fixed (n : ℕ)
    (x : projectionRankStratum P b n) (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    P x.val (projectionStratumSynthesis P hP b hb n x v) =
      projectionStratumSynthesis P hP b hb n x v := by
  obtain ⟨w, hw⟩ := ((projectionStratumCoordinates P hP b hb n x).symm v).property
  change P x.val (((projectionStratumCoordinates P hP b hb n x).symm v : (P x.val).range) : H) = _
  change P x.val (((projectionStratumCoordinates P hP b hb n x).symm v : (P x.val).range) : H) =
    (((projectionStratumCoordinates P hP b hb n x).symm v : (P x.val).range) : H)
  rw [← hw]
  exact congrArg (fun T : H →L[ℂ] H => T w) (hP x.val)

theorem projectionStratumAnalysis_synthesis (n : ℕ)
    (x : projectionRankStratum P b n) (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    projectionStratumAnalysis P hP b hb n x
      (projectionStratumSynthesis P hP b hb n x v) = v := by
  apply (projectionStratumSynthesis P hP b hb n x).injective
  rw [projectionStratumSynthesis_analysis, projectionStratumSynthesis_fixed]

theorem projectionStratumAnalysis_apply_norm_le (n : ℕ)
    (x : projectionRankStratum P b n) (v : H) :
    ‖projectionStratumAnalysis P hP b hb n x v‖ ≤ ‖P x.val‖ * ‖v‖ := by
  change ‖projectionStratumCoordinates P hP b hb n x ((P x.val).rangeRestrict v)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (P x.val).le_opNorm v

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem projectionStratumSynthesis_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    Measurable fun x => projectionStratumSynthesis P hP b hb n x v :=
  projectionStratumCoordinates_symm_measurable P hP b hb hPm n
    (fun _ => v) (fun _ => measurable_const)

theorem projectionStratumAnalysis_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    [MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ)]
    [BorelSpace ℓ²(projectionDimensionIndex n, ℂ)] (v : H) :
    Measurable fun x => projectionStratumAnalysis P hP b hb n x v := by
  exact projectionStratumCoordinates_measurable P hP b hb hPm n
    (fun x => ⟨P x.val v, ⟨v, rfl⟩⟩) ((hPm v).comp measurable_subtype_coe)

def l2ProjectionStratumSynthesis
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) :
    Lp ℓ²(projectionDimensionIndex n, ℂ) 2 μ →ₗᵢ[ℂ] Lp H 2 μ :=
  l2IsometryField μ (projectionStratumSynthesis P hP b hb n)
    (fun v => (projectionStratumSynthesis_measurable P hP b hb hPm n v).aestronglyMeasurable)

theorem l2ProjectionStratumSynthesis_ae
    (hPm : ∀ v, Measurable fun x => P x v) (n : ℕ)
    (μ : Measure (projectionRankStratum P b n))
    (f : Lp ℓ²(projectionDimensionIndex n, ℂ) 2 μ) :
    l2ProjectionStratumSynthesis P hP b hb hPm n μ f =ᵐ[μ]
      fun x => projectionStratumSynthesis P hP b hb n x (f x) :=
  l2IsometryField_ae μ _ _ f

end

end KadisonKastler

end OAI
