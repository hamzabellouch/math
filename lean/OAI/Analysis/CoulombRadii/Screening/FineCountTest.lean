import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CountMoments
import OAI.Analysis.CoulombRadii.ThomasFermi.TFCountTest

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma fineKernel_eq_zero_of_two_mul_lt {b : ℝ} (hb : 0<b) (z : Space) (hz : 2*b<‖z‖) :
    fineKernel b z=0 := by
  apply fineKernel_eq_zero hb
  nlinarith [sq_nonneg (‖z‖-2*b)]

lemma retainedFineDensity_memLp {n : ℕ} {b : ℝ} (hb : 0<b)
    (r : Finset (Fin n)) (x : Fin n → Space) {Ω : Set Space}
    [IsFiniteMeasure (volume.restrict Ω)] :
    MemLp (retainedFineDensity b r x) TFExponent (volume.restrict Ω) := by
  apply MemLp.of_bound ((retainedFineDensity_measurable b r x).aestronglyMeasurable) ((n:ℝ)*(b⁻¹)^3)
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (retainedFineDensity_nonneg ..)]
  apply (retainedFineDensity_le ..).trans
  unfold fineDensity
  calc
    _≤∑ _i : Fin n, (b⁻¹)^3 := Finset.sum_le_sum (fun _ _ => fineKernel_le hb _)
    _=_ := by simp

def patchRetained {n : ℕ} (y : Space) (t b : ℝ) (x : Configuration n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ‖position x i-y‖<t-7*b)

lemma patchRetained_mem {n : ℕ} (y : Space) (t b : ℝ) (x : Configuration n) (i : Fin n) :
    i∈patchRetained y t b x ↔ ‖position x i-y‖<t-7*b := by simp [patchRetained]

lemma patchRetained_measurable {n : ℕ} (y : Space) (t b : ℝ) (i : Fin n) :
    MeasurableSet {x : Configuration n | i∈patchRetained y t b x} := by
  simp only [patchRetained_mem]
  exact measurableSet_lt (((continuous_position i).sub continuous_const).norm.measurable) measurable_const

lemma retainedFineDensity_patch_support {n : ℕ} {b : ℝ} (hb : 0<b)
    (y : Space) (t : ℝ) (x : Configuration n) (z : Space)
    (hz : z∉Metric.ball y (t-4*b)) :
    retainedFineDensity b (patchRetained y t b x) (position x) z=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply fineKernel_eq_zero_of_two_mul_lt hb
  have hc := (patchRetained_mem y t b x i).mp hi
  have hn : t-4*b≤‖z-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hz
  have htri := norm_sub_le_norm_sub_add_norm_sub z (position x i) y
  linarith

lemma deletedLabels_patchRetained {n : ℕ} (y : Space) (t b : ℝ) (x : Configuration n) :
    ((deletedLabels (patchRetained y t b) x).card:ℝ)=localCount {z | t-7*b≤‖z-y‖} x := by
  have he : deletedLabels (patchRetained y t b) x=Finset.univ.filter (fun i => t-7*b≤‖position x i-y‖) := by
    ext i
    simp [deletedLabels,patchRetained,not_lt]
  rw [he]
  simp only [Finset.card_eq_sum_ones,Nat.cast_sum,Finset.sum_filter,localCount,Set.indicator_apply,Set.mem_ofPred_eq]
  simp

lemma fineKernel_countTest_one {a b : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 4*b≤a)
    (y : Space) {w : Space} (hw : ‖w-y‖≤a) :
    (∫ z, fineKernel b (z-w)*countTest y (3*a/2) z)=1 := by
  rw [←fineKernel_shift_integral hb w]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : fineKernel b (z-w)=0
  · simp only [hz,zero_mul]
  have hn : ‖z-w‖≤2*b := le_of_not_gt (fun h => hz (fineKernel_eq_zero_of_two_mul_lt hb _ h))
  rw [countTest_one y (by positivity) (le_trans (norm_sub_le_norm_sub_add_norm_sub z w y) (by linarith)),mul_one]

lemma localCount_le_fine_test {n : ℕ} {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    (hsmall : 4*b≤a) (ht : a<t-7*b) (y : Space) (x : Configuration n) :
    localCount (Metric.closedBall y a) x≤
      ∫ z, retainedFineDensity b (patchRetained y t b x) (position x) z*countTest y (3*a/2) z := by
  simp only [retainedFineDensity,Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => integrable_mul_countTest (fineKernel_shift_integrable hb _) y (3*a/2))]
  have hr : localCount (Metric.closedBall y a) x=
      ∑ i∈patchRetained y t b x, (Metric.closedBall y a).indicator (fun _ => (1:ℝ)) (position x i) := by
    unfold localCount
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i hi hn
    apply indicator_of_notMem
    intro hm
    apply hn
    apply (patchRetained_mem ..).mpr
    have hh : ‖position x i-y‖≤a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hm
    exact hh.trans_lt ht
  rw [hr]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hm : position x i∈Metric.closedBall y a
  · rw [indicator_of_mem hm,fineKernel_countTest_one ha hb hsmall y (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hm)]
  · rw [indicator_of_notMem hm]
    exact integral_nonneg (fun z => mul_nonneg (fineKernel_nonneg ..) (countTest_nonneg ..))

end Coulomb
end

end
end

end OAI
