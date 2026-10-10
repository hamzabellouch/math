import OAI.Analysis.CircleDomains.Rigidity.MatchedSliceCover
import OAI.Analysis.CircleDomains.Rigidity.AxialTargetDiskMeasure
import OAI.Analysis.CircleDomains.Sobolev.SmoothClosedSliceImage
import OAI.Analysis.CircleDomains.Probability.IntervalCoverMeasure

namespace OAI

/-! The numerical slice estimate for the actual matched correspondence.
Only disks meeting the segment are charged. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem scalar_slice_estimate [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {φ : Sphere → ℝ} (hφ : Continuous φ)
    (k : Fin 2) (hcoord : ∀ p ∈ (f '' G)ᶜ,
      φ p = (complexPlaneCoordinates.symm (finiteCoord p)) k)
    {a b : ℝ} (hab : a ≤ b) (F : Finset D.IndexedMatchedPair)
    (havoid : ∀ x ∈ Icc a b, ∀ j ∈ F, (γ x : Sphere) ∉ j.val.1)
    (hnull : volume ((fun x => φ (D.selectedTarget hG.1 hf (γ x : Sphere))) ''
      {x | γ x ∈ D.commonPointPlane}) = 0)
    (hsmooth : ContDiffOn ℝ 1 (fun x => φ (f (γ x : Sphere)))
      {x | (γ x : Sphere) ∈ G})
    (hi : IntegrableOn (fun x => |deriv (fun t => φ (f (γ t : Sphere))) x|)
      (Icc a b ∩ {x | (γ x : Sphere) ∈ G}) volume)
    (hsum : Summable (fun j : {j : D.IndexedMatchedPair // j ∉ F} =>
      if ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1 then 2*E.targetRadius j else 0)) :
    |φ (D.selectedTarget hG.1 hf (γ b : Sphere))-
        φ (D.selectedTarget hG.1 hf (γ a : Sphere))| ≤
      (∫ x in Icc a b ∩ {x | (γ x : Sphere) ∈ G},
        |deriv (fun t => φ (f (γ t : Sphere))) x|) +
      ∑' j : {j : D.IndexedMatchedPair // j ∉ F},
        if ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1 then 2*E.targetRadius j else 0 := by
  classical
  have hV : IsOpen {x | (γ x : Sphere) ∈ G} :=
    hG.1.preimage (OnePoint.continuous_coe.comp hγ)
  apply interval_length_le_integral_and_tolls
    (I := fun j : {j : D.IndexedMatchedPair // j ∉ F} =>
      if ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1 then φ '' j.val.val.2 else ∅)
    (integral_nonneg (fun _ => abs_nonneg _))
    (fun j => by split_ifs <;> [exact mul_nonneg (by norm_num) (E.target_nonneg j); exact le_rfl]) hsum
  · apply measure_mono_null (image_mono (inter_subset_right (s := Icc a b))) hnull
  · exact smooth_closed_slice_image_measure_le hV hsmooth hi
  · intro j
    by_cases hj : ∃ x ∈ Icc a b, (γ x : Sphere) ∈ j.val.val.1
    · simp only [ite_eq_left hj]
      exact E.target_scalar_image_measure_le k j hcoord
    · simp only [ite_eq_right hj,measure_empty,ENNReal.ofReal_zero,le_refl]
  · exact D.scalar_slice_cover hG hinf hf hH hinf' hγ hφ hab F havoid

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
