import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonRadii
import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonCutoff

namespace OAI

/-! Construct each complete balloon system: shrinking radii, a smooth
cutoff around every closed component, and one square-integrable density
paying all finite sums of the cutoff derivatives. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def traceBalloonInnerRatio (m : ℕ) : ℝ := (2*(m:ℝ)+3)/(2*(m:ℝ)+4)

 theorem traceBalloonInnerRatio_bounds (m : ℕ) :
    0 < traceBalloonInnerRatio m ∧ traceBalloonInnerRatio m < 1 := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · exact div_pos (by positivity) (by positivity)
  · apply (div_lt_one (by positivity)).mpr
    linarith

 theorem traceBalloonRadius_inner {r : ℕ → ℝ} (hr : ∀ j, 0 ≤ r j) (m j : ℕ) :
    r j < traceBalloonInnerRatio m*traceBalloonRadius r m j := by
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  by_cases hj : 0 < r j
  · simp only [traceBalloonRadius,ite_eq_left hj,traceBalloonInnerRatio]
    have he : (2*(m:ℝ)+3)/(2*(m:ℝ)+4)*(1+1/((m:ℝ)+1))*r j =
        r j+(r j)/(2*((m:ℝ)+1)) := by field_simp; ring
    rw [← mul_assoc,he]
    exact lt_add_of_pos_right _ (div_pos hj (by positivity))
  · have hz : r j = 0 := le_antisymm (le_of_not_gt hj) (hr j)
    rw [hz]
    exact mul_pos (traceBalloonInnerRatio_bounds m).1 (traceBalloonRadius_pos m j)

 theorem exists_trace_balloon_system (hmax : PlanarMaximalL2)
    (c : ℕ → ℂ) (r a : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (ha : ∀ j, 0 ≤ a j)
    (hdisj : Pairwise (Disjoint on fun j => ball (c j) (r j)))
    (hr2 : Summable (fun j => r j^2)) (ha2 : Summable (fun j => a j^2)) (m : ℕ) :
    ∃ (C : ℝ) (cutoff : ℕ → ℂ → ℝ) (P : ℂ → ℝ), 0 < C ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (cutoff j)) ∧ (∀ j z, cutoff j z ∈ Icc (0:ℝ) 1) ∧
      (∀ j z, ‖z-c j‖ ≤ traceBalloonInnerRatio m*traceBalloonRadius r m j → cutoff j z = 0) ∧
      (∀ j z, traceBalloonRadius r m j ≤ ‖z-c j‖ → cutoff j z = 1) ∧
      (∀ j z, ‖fderiv ℝ (cutoff j) z‖ ≤
        (ball (c j) (traceBalloonRadius r m j)).indicator (fun _ => C/traceBalloonRadius r m j) z) ∧
      Measurable P ∧ (∀ z, 0 ≤ P z) ∧ MemLp P 2 volume ∧
      (∀ᵐ z ∂volume, ∀ n, (∑ j ∈ Finset.range n, a j*‖fderiv ℝ (cutoff j) z‖) ≤ P z) := by
  obtain ⟨C,hC,hcut⟩ := exists_trace_balloon_cutoffs
    (traceBalloonInnerRatio_bounds m).1 (traceBalloonInnerRatio_bounds m).2
  choose cutoff hs hu hz ho hg using (fun j => hcut (c j) (traceBalloonRadius r m j) (traceBalloonRadius_pos m j))
  obtain ⟨P,hPm,hP0,hP2,hPb⟩ := exists_trace_balloon_density hmax c r
    (traceBalloonRadius r m) a hr (fun j => traceBalloonRadius_pos m j) ha
    (fun j => (traceBalloonRadius_lt hr m j).le) (fun j => traceBalloonRadius_le_double m j)
    hdisj ha2 (traceBalloonRadius_summable_sq hr2 m) (fun j => traceBalloonRadius_zero_tail m j)
  refine ⟨C,cutoff,(fun z => C*P z),hC,hs,hu,hz,ho,hg,
    measurable_const.mul hPm,(fun z => mul_nonneg hC.le (hP0 z)),hP2.const_mul C,?_⟩
  filter_upwards [hPb] with z hzb
  intro n
  calc
    _ ≤ ∑ j ∈ Finset.range n, a j*(ball (c j) (traceBalloonRadius r m j)).indicator
        (fun _ => C/traceBalloonRadius r m j) z :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hg j z) (ha j))
    _ = C*finiteBallDensity (Finset.range n) c (traceBalloonRadius r m) a z := by
      rw [finiteBallDensity,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : z ∈ ball (c j) (traceBalloonRadius r m j)
      · simp only [indicator_of_mem h]
        ring
      · simp only [indicator_of_notMem h,mul_zero]
    _ ≤ C*P z := mul_le_mul_of_nonneg_left (hzb n) hC.le

end CircleDomainRigidity

end

end OAI
