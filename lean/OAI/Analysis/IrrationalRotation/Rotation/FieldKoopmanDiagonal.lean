import OAI.Analysis.IrrationalRotation.Analysis.FieldKoopman
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.FieldKoopman
open WeightedShift DirectIntegral
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem commute_fieldShift (σ : X → X) (hσ : MeasurePreserving σ μ μ) :
    Commute ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ)
      (shiftedPullback (shift 1).toLinearIsometry.toContinuousLinearMap σ hσ) :=
  commute_const _ _ σ hσ (Commute.refl _)

theorem commute_fieldShifts (m n : ℤ) (σ : X → X)
    (hσ : MeasurePreserving σ μ μ) :
    Commute ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ)
      (shiftedPullback (shift n).toLinearIsometry.toContinuousLinearMap σ hσ) := by
  apply commute_const
  change (shift m).toLinearIsometry.toContinuousLinearMap *
      (shift n).toLinearIsometry.toContinuousLinearMap =
    (shift n).toLinearIsometry.toContinuousLinearMap *
      (shift m).toLinearIsometry.toContinuousLinearMap
  rw [← shift_add, ← shift_add, add_comm m n]

theorem commute_fieldDiagonal
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (m : ℤ) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (hcoeff : ∀ᵐ x ∂μ, ∀ k : ℤ, a (σ x) (k - m) = a x k) :
    Commute (fieldDiagonal a C hC ha hm)
      (shiftedPullback (shift m).toLinearIsometry.toContinuousLinearMap σ hσ) := by
  apply commute_of_represented_covariance (fieldDiagonal a C hC ha hm)
    (fun x => diagonal (a x)) (fieldDiagonal_ae a C hC ha hm)
    (shift m).toLinearIsometry.toContinuousLinearMap σ hσ
  filter_upwards [hcoeff] with x hx
  ext ξ k
  change a x k * ξ (k - m) = a (σ x) (k - m) * ξ (k - m)
  rw [hx k]

theorem shift_default_basis (m k : ℤ) :
    shift m ((default : HilbertBasis ℤ ℂ Hilbert) k) =
      (default : HilbertBasis ℤ ℂ Hilbert) (k + m) := by
  have hb (i : ℤ) : (default : HilbertBasis ℤ ℂ Hilbert) i =
      (lp.single 2 i (1 : ℂ) : Hilbert) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Hilbert) i).symm
  rw [hb, hb]
  ext j
  change (lp.single 2 k (1 : ℂ) : Hilbert) (j - m) =
    (lp.single 2 (k + m) (1 : ℂ) : Hilbert) j
  simp [lp.single_apply, Pi.single_apply, sub_eq_iff_eq_add]

end Invariant233.FieldKoopman

end

end OAI
