import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem cos_strip_near_zero {x c t : ℝ} (hc : Real.cos c = 0)
    (hs : |Real.sin c| = 1) (hnear : |x-c| ≤ Real.pi/2)
    (ht : |Real.cos x| ≤ t) : |x-c| ≤ Real.pi/2*t := by
  have hh := Real.mul_abs_le_abs_sin hnear
  have he : |Real.sin (x-c)| = |Real.cos x| := by
    rw [Real.sin_sub,hc,mul_zero,zero_sub,abs_neg,abs_mul,hs,mul_one]
  rw [he] at hh
  have hp := Real.pi_pos
  have hi : (2/Real.pi:ℝ)*Real.pi = 2 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right (hh.trans ht) hp.le]

theorem cos_strip_four_intervals {x t : ℝ} (hx : -Real.pi ≤ x ∧ x ≤ 3*Real.pi)
    (ht : |Real.cos x| ≤ t) :
    |x-(-Real.pi/2)| ≤ Real.pi/2*t ∨
    |x-(Real.pi/2)| ≤ Real.pi/2*t ∨
    |x-(Real.pi/2+Real.pi)| ≤ Real.pi/2*t ∨
    |x-(Real.pi/2+2*Real.pi)| ≤ Real.pi/2*t := by
  have hp := Real.pi_pos
  by_cases h0 : x ≤ 0
  · left
    apply cos_strip_near_zero _ _ _ ht
    · simp [neg_div,Real.cos_neg]
    · simp [neg_div,Real.sin_neg]
    · rw [abs_le]; constructor <;> linarith
  by_cases h1 : x ≤ Real.pi
  · right; left
    apply cos_strip_near_zero (by simp) (by simp) _ ht
    rw [abs_le]; constructor <;> linarith
  by_cases h2 : x ≤ 2*Real.pi
  · right; right; left
    apply cos_strip_near_zero (by simp) (by simp) _ ht
    rw [abs_le]; constructor <;> linarith
  · right; right; right
    apply cos_strip_near_zero (by simp) (by simp) _ ht
    rw [abs_le]; constructor <;> linarith

theorem volume_cos_strip {a t : ℝ} (ha : -Real.pi ≤ a ∧ a ≤ Real.pi) (ht : 0 ≤ t) :
    volume {θ : ℝ | θ ∈ Ioc 0 (2*Real.pi) ∧ |Real.cos (θ-a)| ≤ t} ≤
      ENNReal.ofReal (4*Real.pi*t) := by
  let r := Real.pi/2*t
  let c0 := a-Real.pi/2
  let c1 := a+Real.pi/2
  let c2 := a+(Real.pi/2+Real.pi)
  let c3 := a+(Real.pi/2+2*Real.pi)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsub : {θ : ℝ | θ ∈ Ioc 0 (2*Real.pi) ∧ |Real.cos (θ-a)| ≤ t} ⊆
      Icc (c0-r) (c0+r) ∪ Icc (c1-r) (c1+r) ∪
      Icc (c2-r) (c2+r) ∪ Icc (c3-r) (c3+r) := by
    intro θ hθ
    have hx : -Real.pi ≤ θ-a ∧ θ-a ≤ 3*Real.pi := by
      obtain ⟨⟨h0,h1⟩,hs⟩ := hθ
      constructor <;> linarith [Real.pi_pos]
    rcases cos_strip_four_intervals hx hθ.2 with h|h|h|h
    · left; left; left
      rw [abs_le] at h
      dsimp [c0,r]; constructor <;> linarith
    · left; left; right
      rw [abs_le] at h
      dsimp [c1,r]; constructor <;> linarith
    · left; right
      rw [abs_le] at h
      dsimp [c2,r]; constructor <;> linarith
    · right
      rw [abs_le] at h
      dsimp [c3,r]; constructor <;> linarith
  calc
    _ ≤ volume (Icc (c0-r) (c0+r) ∪ Icc (c1-r) (c1+r) ∪
        Icc (c2-r) (c2+r) ∪ Icc (c3-r) (c3+r)) := measure_mono hsub
    _ ≤ ((volume (Icc (c0-r) (c0+r))+volume (Icc (c1-r) (c1+r)))+
        volume (Icc (c2-r) (c2+r)))+volume (Icc (c3-r) (c3+r)) := by
      apply (measure_union_le _ _).trans
      gcongr
      apply (measure_union_le _ _).trans
      gcongr
      exact measure_union_le _ _
    _ = ENNReal.ofReal (4*Real.pi*t) := by
      simp only [Real.volume_Icc]
      have he (c : ℝ) : c+r-(c-r) = 2*r := by ring
      simp only [he]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp [r]
      ring

end PlanarFalconer

end OAI
