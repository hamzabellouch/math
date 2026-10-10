import OAI.Analysis.IrrationalRotation.Rotation.FieldWeightedShiftHalfline
import OAI.Analysis.IrrationalRotation.Model.ShiftedPullback

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem commute_of_constantField_commute_shiftedPullback
    [IsFiniteMeasure μ] [NeZero μ]
    (A S : Hilbert →L[ℂ] Hilbert) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ)
    (h : Commute (A.compLpL 2 μ) (DirectIntegral.shiftedPullback S σ hσ)) :
    Commute A S := by
  have hJ (f : Lp Hilbert 2 μ) :
      DirectIntegral.shiftedPullback S σ hσ f =ᵐ[μ] fun x => S (f (σ x)) := by
    filter_upwards [S.coeFn_compLpL (Lp.compMeasurePreserving σ hσ f),
      Lp.coeFn_compMeasurePreserving f hσ] with x hSx hσx
    exact hSx.trans (congrArg S hσx)
  change A * S = S * A
  apply ContinuousLinearMap.ext
  intro v
  let f : Lp Hilbert 2 μ := Lp.const 2 μ v
  have hconst : ∀ᵐ x ∂μ, f (σ x) = v :=
    hσ.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ v)
  have hA : ∀ᵐ x ∂μ, A.compLpL 2 μ f (σ x) = A (f (σ x)) :=
    hσ.quasiMeasurePreserving.ae (constantField_ae A f)
  have he : ∀ᵐ x ∂μ, A (S v) = S (A v) := by
    filter_upwards [constantField_ae A (DirectIntegral.shiftedPullback S σ hσ f),
      hJ f, hJ (A.compLpL 2 μ f), hconst, hA] with x ha hj hja hc haf
    have hex := congrArg
      (fun T : Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ => T f x) h.eq
    change A.compLpL 2 μ (DirectIntegral.shiftedPullback S σ hσ f) x =
      DirectIntegral.shiftedPullback S σ hσ (A.compLpL 2 μ f) x at hex
    rw [ha, hj, hja, haf, hc] at hex
    exact hex
  exact he.exists.choose_spec

theorem tailProjection_not_commute_shift (m : ℤ) :
    ¬ Commute (tailProjection m) (shift 1).toLinearIsometry.toContinuousLinearMap := by
  intro h
  have he := congrArg
    (fun T : Hilbert →L[ℂ] Hilbert => T (lp.single 2 (m-1) 1) m) h.eq
  have hm : ¬ m ≤ m-1 := by omega
  change (tailProjection m (shift 1 (lp.single 2 (m-1) 1))) m =
    (shift 1 (tailProjection m (lp.single 2 (m-1) 1))) m at he
  simp [shift_apply, hm] at he

theorem fieldTailProjection_not_commute_shiftedPullback
    [IsFiniteMeasure μ] [NeZero μ] (m : ℤ) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ) :
    ¬ Commute (fieldTailProjection (μ := μ) m)
      (DirectIntegral.shiftedPullback
        (shift 1).toLinearIsometry.toContinuousLinearMap σ hσ) := by
  intro h
  exact tailProjection_not_commute_shift m
    (commute_of_constantField_commute_shiftedPullback _ _ σ hσ h)

end Invariant233.WeightedShift

end

end OAI
