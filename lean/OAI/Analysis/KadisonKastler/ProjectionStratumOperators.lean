import OAI.Analysis.KadisonKastler.ProjectionDimensionStrata
import OAI.Analysis.KadisonKastler.PolishConjugacyRelation

namespace OAI

/-! # Transporting measurable operators to fixed dimension coordinates -/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction to an invariant projection range, retaining the original norm. -/
def projectionRangeRestriction (P T : H →L[ℂ] H)
    (hT : ∀ v ∈ P.range, T v ∈ P.range) : P.range →L[ℂ] P.range :=
  (T.comp P.range.subtypeL).codRestrict P.range (fun v => hT v v.property)

omit [CompleteSpace H] in
@[simp] theorem projectionRangeRestriction_coe (P T : H →L[ℂ] H)
    (hT : ∀ v ∈ P.range, T v ∈ P.range) (v : P.range) :
    (projectionRangeRestriction P T hT v : H) = T v := rfl

omit [CompleteSpace H] in
theorem projectionRangeRestriction_norm_le (P T : H →L[ℂ] H)
    (hT : ∀ v ∈ P.range, T v ∈ P.range) :
    ‖projectionRangeRestriction P T hT‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro v
  exact T.le_opNorm v

variable (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

/-- An invariant operator field in a fixed Hilbert space on each rank stratum. -/
def projectionStratumOperator (T : X → H →L[ℂ] H)
    (hT : ∀ x v, v ∈ (P x).range → T x v ∈ (P x).range)
    (n : ℕ) (x : projectionRankStratum P b n) :
    ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ) := by
  letI : CompleteSpace (P x.val).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hP x.val)).completeSpace_coe
  exact (projectionStratumCoordinates P hP b hb n x).conjStarAlgEquiv
    (projectionRangeRestriction (P x.val) (T x.val) (hT x.val))

@[simp] theorem projectionStratumOperator_apply (T : X → H →L[ℂ] H)
    (hT : ∀ x v, v ∈ (P x).range → T x v ∈ (P x).range)
    (n : ℕ) (x : projectionRankStratum P b n) (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    projectionStratumOperator P hP b hb T hT n x v =
      projectionStratumCoordinates P hP b hb n x
        (projectionRangeRestriction (P x.val) (T x.val) (hT x.val)
          ((projectionStratumCoordinates P hP b hb n x).symm v)) := by
  simp only [projectionStratumOperator, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

theorem projectionStratumOperator_norm_le (T : X → H →L[ℂ] H)
    (hT : ∀ x v, v ∈ (P x).range → T x v ∈ (P x).range)
    (n : ℕ) (x : projectionRankStratum P b n) :
    ‖projectionStratumOperator P hP b hb T hT n x‖ ≤ ‖T x.val‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [projectionStratumOperator_apply, LinearIsometryEquiv.norm_map]
  change ‖T x.val ((projectionStratumCoordinates P hP b hb n x).symm v : H)‖ ≤ _
  simpa only [Submodule.norm_coe, LinearIsometryEquiv.norm_map] using
    (T x.val).le_opNorm ((projectionStratumCoordinates P hP b hb n x).symm v : H)

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]

theorem projectionStratumOperator_measurable
    (hPm : ∀ v, Measurable fun x => P x v) (T : X → H →L[ℂ] H)
    (hTm : ∀ v, Measurable fun x => T x v)
    (hT : ∀ x v, v ∈ (P x).range → T x v ∈ (P x).range)
    (n : ℕ) [MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ)]
    [BorelSpace ℓ²(projectionDimensionIndex n, ℂ)]
    (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    Measurable fun x => projectionStratumOperator P hP b hb T hT n x v := by
  have hv : Measurable fun x : projectionRankStratum P b n =>
      ((projectionStratumCoordinates P hP b hb n x).symm v : H) :=
    projectionStratumCoordinates_symm_measurable P hP b hb hPm n (fun _ => v)
      (fun _ => measurable_const)
  have hTv := measurable_operator_field_apply
    (fun x : projectionRankStratum P b n => T x.val)
    (fun w => (hTm w).comp measurable_subtype_coe) _ hv
  have hc := projectionStratumCoordinates_measurable P hP b hb hPm n
    (fun x => projectionRangeRestriction (P x.val) (T x.val) (hT x.val)
      ((projectionStratumCoordinates P hP b hb n x).symm v)) hTv
  simpa only [projectionStratumOperator_apply] using hc

end

end KadisonKastler

end OAI
