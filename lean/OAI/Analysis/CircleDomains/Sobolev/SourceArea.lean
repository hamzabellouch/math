import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The source-area inequality for circle domains

The source region and the interiors of its complementary disks are
disjoint subsets of one outer disk. Countable additivity gives the
source-area inequality used in Section 6 of the rigidity manuscript.
No regularity of the remaining point components is needed.
-/

open MeasureTheory Metric Set Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Countable additivity for a disjoint measurable family, together with
one further disjoint source set, gives an area bound in a containing set. -/
theorem measure_source_add_disks_le {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) {U O : Set X} (D : ι → Set X)
    (hD : ∀ j, MeasurableSet (D j))
    (hpair : Pairwise (Disjoint on D))
    (hdisj : ∀ j, Disjoint U (D j))
    (hUO : U ⊆ O) (hDO : ∀ j, D j ⊆ O) :
    μ U + ∑' j, μ (D j) ≤ μ O := by
  have hd : Disjoint U (⋃ j, D j) := disjoint_iUnion_right.mpr hdisj
  calc
    μ U + ∑' j, μ (D j) = μ (U ∪ ⋃ j, D j) := by
      rw [measure_union hd (MeasurableSet.iUnion hD), measure_iUnion hpair hD]
    _ ≤ μ O := measure_mono (union_subset hUO (iUnion_subset hDO))

/-- The actual geometric source-area bound for pairwise disjoint disks. -/
theorem sourceArea_le {ι : Type*} [Countable ι] {U : Set ℂ}
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hdisj : ∀ j, Disjoint U (ball (centers j) (radii j)))
    (hUO : U ⊆ ball 0 R)
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    volume U + ∑' j, volume (ball (centers j) (radii j)) ≤ volume (ball (0 : ℂ) R) :=
  measure_source_add_disks_le volume (fun j => ball (centers j) (radii j))
    (fun _ => measurableSet_ball) hpair hdisj hUO hDO

/-- Planar ball area, expressed as an ordinary real number. -/
theorem real_volume_ball (center : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball center r)).toReal = Real.pi * r ^ 2 := by
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-- Finitely bounded, pairwise disjoint disks have square-summable radii. -/
theorem summable_radii_sq {ι : Type*} [Countable ι]
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hr : ∀ j, 0 ≤ radii j)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    Summable (fun j => radii j ^ 2) := by
  have hbound := sourceArea_le (U := ∅) centers radii R hpair
    (fun _ => by simp) (empty_subset _) hDO
  simp only [measure_empty, zero_add] at hbound
  have hfinite : (∑' j, volume (ball (centers j) (radii j))) ≠ ∞ :=
    ne_of_lt (hbound.trans_lt (measure_ball_lt_top))
  have hs := ENNReal.summable_toReal hfinite
  have hs' : Summable (fun j => Real.pi * radii j ^ 2) :=
    hs.congr (fun j => real_volume_ball (centers j) (hr j))
  exact (summable_mul_left_iff Real.pi_ne_zero).mp hs'

/-- The real source-area inequality, with the familiar factor `π`. -/
theorem sourceArea_real_le {ι : Type*} [Countable ι] {U : Set ℂ}
    (centers : ι → ℂ) (radii : ι → ℝ) (R : ℝ)
    (hr : ∀ j, 0 ≤ radii j) (hR : 0 ≤ R)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (radii j)))
    (hdisj : ∀ j, Disjoint U (ball (centers j) (radii j)))
    (hUO : U ⊆ ball 0 R)
    (hDO : ∀ j, ball (centers j) (radii j) ⊆ ball 0 R) :
    (volume U).toReal + Real.pi * (∑' j, radii j ^ 2) ≤ Real.pi * R ^ 2 := by
  have hbound := sourceArea_le centers radii R hpair hdisj hUO hDO
  have hsumBound : (∑' j, volume (ball (centers j) (radii j))) ≤
      volume (ball (0 : ℂ) R) :=
    le_trans (le_add_left le_rfl) hbound
  have hfinite : (∑' j, volume (ball (centers j) (radii j))) ≠ ∞ :=
    ne_of_lt (hsumBound.trans_lt measure_ball_lt_top)
  have hUfinite : volume U ≠ ∞ :=
    ne_of_lt ((measure_mono hUO).trans_lt measure_ball_lt_top)
  have hreal := ENNReal.toReal_mono (ne_of_lt measure_ball_lt_top) hbound
  rw [ENNReal.toReal_add hUfinite hfinite,
    ENNReal.tsum_toReal_eq (fun _ => ne_of_lt measure_ball_lt_top),
    real_volume_ball 0 hR] at hreal
  have heq : (∑' j, (volume (ball (centers j) (radii j))).toReal) =
      Real.pi * (∑' j, radii j ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    exact real_volume_ball (centers j) (hr j)
  rw [heq] at hreal
  exact hreal

end CircleDomainRigidity

end OAI
