import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightIdentification
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelRestart

namespace OAI

/-! # The bounded inverse of each finite-time expanding free step

This inverse is only used on finite slabs, to remove the free evolution
before differentiating a continuous forced solution in its energy norm.
-/

open Set Filter Topology

namespace DefocusingNLS

noncomputable def expandingFreeInverse (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t) :
    FourierL2 →L[ℂ] FourierL2 :=
  (expandingFreeAmplitude a b t)⁻¹ •
    ((schrodingerFlow (-expandingFreeTime L t)).toContinuousLinearMap.comp
      ((expandingScaleTransfer a k 1 L ha hk le_rfl hL).comp
        (expandingInverseTransfer a k (expandingRadius L t) ha hk
          (hL.trans (expandingRadius_ge L t hL ht)))))

theorem expandingFreeInverse_apply (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t) (f : FourierL2) :
    expandingFreeInverse a b k L t ha hk hL ht f =
      (expandingFreeAmplitude a b t)⁻¹ • schrodingerFlow (-expandingFreeTime L t)
        (expandingScaleTransfer a k 1 L ha hk le_rfl hL
          (expandingInverseTransfer a k (expandingRadius L t) ha hk
            (hL.trans (expandingRadius_ge L t hL ht)) f)) := rfl

theorem expandingFreeInverse_coefficient (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (f : FourierL2) (n : frequencyLattice) :
    expandingFreeInverse a b k L t ha hk hL ht f n =
      (expandingFreeAmplitude a b t)⁻¹ * schrodingerMultiplier (-expandingFreeTime L t) n *
        ((expandingSobolevWeight a k L n / expandingSobolevWeight a k (expandingRadius L t) n : ℝ) : ℂ) * f n := by
  change (expandingFreeAmplitude a b t)⁻¹ *
    (schrodingerMultiplier (-expandingFreeTime L t) n *
      ((expandingScaleRatio a k 1 L n : ℂ) *
        ((expandingInverseRatio a k (expandingRadius L t) n : ℂ) * f n))) = _
  unfold expandingScaleRatio expandingInverseRatio
  push_cast
  have h1 := Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k 1 le_rfl n).ne'
  field_simp

private theorem expandingFree_phase_inverse (t : ℝ) (n : frequencyLattice) :
    schrodingerMultiplier (-t) n * schrodingerMultiplier t n = 1 := by
  rw [← schrodingerMultiplier_add, neg_add_cancel, schrodingerMultiplier_zero]

theorem expandingFreeInverse_left (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t) (f : FourierL2) :
    expandingFreeInverse a b k L t ha hk hL ht
      (expandingFreeStep a b k L t ha hk hL ht f) = f := by
  ext n
  rw [expandingFreeInverse_coefficient]
  change (expandingFreeAmplitude a b t)⁻¹ * _ * _ *
    (expandingFreeAmplitude a b t *
      ((expandingScaleRatio a k L (expandingRadius L t) n : ℂ) *
        (schrodingerMultiplier (expandingFreeTime L t) n * f n))) = f n
  unfold expandingScaleRatio
  push_cast
  have hA : expandingFreeAmplitude a b t ≠ 0 := Complex.exp_ne_zero _
  have hW := Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL n).ne'
  have hV := Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k _
    (hL.trans (expandingRadius_ge L t hL ht)) n).ne'
  have hphase := expandingFree_phase_inverse (expandingFreeTime L t) n
  calc
    _ = (schrodingerMultiplier (-expandingFreeTime L t) n *
      schrodingerMultiplier (expandingFreeTime L t) n) * f n := by field_simp
    _ = _ := by rw [hphase, one_mul]

theorem expandingFreeInverse_right (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t) (f : FourierL2) :
    expandingFreeStep a b k L t ha hk hL ht
      (expandingFreeInverse a b k L t ha hk hL ht f) = f := by
  have hleft : Function.LeftInverse
      (expandingFreeInverse a b k L t ha hk hL ht)
      (expandingFreeStep a b k L t ha hk hL ht) :=
    expandingFreeInverse_left a b k L t ha hk hL ht
  have hinj : Function.Injective (expandingFreeInverse a b k L t ha hk hL ht) := by
    intro u v huv
    ext n
    have hn := congrArg (fun g : FourierL2 => g n) huv
    rw [expandingFreeInverse_coefficient, expandingFreeInverse_coefficient] at hn
    apply mul_left_cancel₀ _ hn
    have hW := Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL n).ne'
    have hV := Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k _
      (hL.trans (expandingRadius_ge L t hL ht)) n).ne'
    have hA : expandingFreeAmplitude a b t ≠ 0 := Complex.exp_ne_zero _
    have hP : schrodingerMultiplier (-expandingFreeTime L t) n ≠ 0 := Complex.exp_ne_zero _
    simpa only [Complex.ofReal_div] using
      mul_ne_zero (mul_ne_zero (inv_ne_zero hA) hP) (div_ne_zero hW hV)
  apply hinj
  exact hleft _

end DefocusingNLS

end OAI
