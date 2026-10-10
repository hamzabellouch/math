import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BoundedSupportEnergy

namespace OAI

/-!
# Smooth annular and exterior weights

Differences of smooth ball cutoffs localize functions to annular regions.
Subtracting a cutoff from a finite-measure set indicator gives an exterior
weight with controlled size, square integrability, and distance from the center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def annularSmoothBallCutoff {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    ContDiffBump a := ⟨r, 2 * r, hr, by linarith⟩

def smoothAnnularWeight {d : ℕ} (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (x : Ambient d) : ℝ := annularSmoothBallCutoff a R hR x - annularSmoothBallCutoff a r hr x

def smoothExteriorWeight {d : ℕ} (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (S : Set (Ambient d)) (x : Ambient d) : ℝ :=
  S.indicator (fun _ => 1) x - annularSmoothBallCutoff a R hR x

theorem annularSmoothBallCutoff_basic {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Measurable (annularSmoothBallCutoff a r hr) ∧
    (∀ x, |annularSmoothBallCutoff a r hr x| ≤ 1) ∧
    (∀ x, dist x a ≤ r → annularSmoothBallCutoff a r hr x = 1) ∧
    (∀ x, 2 * r ≤ dist x a → annularSmoothBallCutoff a r hr x = 0) := by
  refine ⟨((annularSmoothBallCutoff a r hr).contDiff (n := ⊤)).continuous.measurable, ?_, ?_, ?_⟩
  · intro x
    rw [abs_of_nonneg (annularSmoothBallCutoff a r hr).nonneg]
    exact (annularSmoothBallCutoff a r hr).le_one
  · intro x hx
    exact (annularSmoothBallCutoff a r hr).one_of_mem_closedBall hx
  · intro x hx
    exact (annularSmoothBallCutoff a r hr).zero_of_le_dist hx

theorem annularSmoothBallCutoff_energy {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    MemLp (annularSmoothBallCutoff a r hr) 2 μ ∧
      (∫ x, annularSmoothBallCutoff a r hr x ^ 2 ∂μ) ≤ G * (2 * r) ^ n := by
  have hb := annularSmoothBallCutoff_basic a r hr
  simpa only [one_pow, one_mul] using! bounded_ball_support_energy n G μ hg _ hb.1
    a (2 * r) 1 (by positivity) (by norm_num) hb.2.1 hb.2.2.2

theorem smoothAnnularWeight_properties {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    MemLp (smoothAnnularWeight a r R hr (hr.trans_le hrR)) 2 μ ∧
    (∀ x, |smoothAnnularWeight a r R hr (hr.trans_le hrR) x| ≤ 1) ∧
    (∀ x, smoothAnnularWeight a r R hr (hr.trans_le hrR) x ≠ 0 → r ≤ dist a x) ∧
    (∫ x, smoothAnnularWeight a r R hr (hr.trans_le hrR) x ^ 2 ∂μ) ≤ G * (2 * R) ^ n := by
  have hR := hr.trans_le hrR
  have hb := annularSmoothBallCutoff_basic a r hr
  have hB := annularSmoothBallCutoff_basic a R hR
  have hm : Measurable (smoothAnnularWeight a r R hr hR) := hB.1.sub hb.1
  have hbound (x : Ambient d) : |smoothAnnularWeight a r R hr hR x| ≤ 1 := by
    have hl := (annularSmoothBallCutoff a r hr).nonneg (x := x)
    have hu := (annularSmoothBallCutoff a r hr).le_one (x := x)
    have hL := (annularSmoothBallCutoff a R hR).nonneg (x := x)
    have hU := (annularSmoothBallCutoff a R hR).le_one (x := x)
    unfold smoothAnnularWeight
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs (x : Ambient d) (hx : 2 * R ≤ dist x a) : smoothAnnularWeight a r R hr hR x = 0 := by
    rw [smoothAnnularWeight, hB.2.2.2 x hx, hb.2.2.2 x (by linarith), sub_self]
  have he := bounded_ball_support_energy n G μ hg _ hm a (2 * R) 1 (by positivity)
    (by norm_num) hbound hs
  refine ⟨he.1, hbound, ?_, by simpa only [one_pow, one_mul] using! he.2⟩
  intro x hx
  by_contra hdist
  have hd : dist x a ≤ r := by rw [dist_comm]; exact (lt_of_not_ge hdist).le
  apply hx
  rw [smoothAnnularWeight, hB.2.2.1 x (hd.trans hrR), hb.2.2.1 x hd, sub_self]

theorem smoothExteriorWeight_properties {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hfin : μ S < ∞)
    (hcontains : ball a (2 * R) ⊆ S) :
    MemLp (smoothExteriorWeight a R hR S) 2 μ ∧
    (∀ x, |smoothExteriorWeight a R hR S x| ≤ 1) ∧
    (∀ x, smoothExteriorWeight a R hR S x ≠ 0 → R ≤ dist a x) := by
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hi : MemLp (S.indicator (fun _ : Ambient d => (1 : ℝ))) 2 μ :=
    (memLp_indicator_iff_restrict hS).mpr (memLp_const 1)
  have hb := annularSmoothBallCutoff_basic a R hR
  refine ⟨hi.sub (annularSmoothBallCutoff_energy n G μ hg a R hR).1, ?_, ?_⟩
  · intro x
    unfold smoothExteriorWeight
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have hl := (annularSmoothBallCutoff a R hR).nonneg (x := x)
      have hu := (annularSmoothBallCutoff a R hR).le_one (x := x)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hd : 2 * R ≤ dist x a := le_of_not_gt (fun h => hx (hcontains h))
      rw [indicator_of_notMem hx, hb.2.2.2 x hd]
      norm_num
  · intro x hx
    by_contra hdist
    have hd : dist x a < R := by rw [dist_comm]; exact lt_of_not_ge hdist
    have hxS : x ∈ S := hcontains (by change dist x a < 2 * R; linarith)
    apply hx
    rw [smoothExteriorWeight, indicator_of_mem hxS, hb.2.2.1 x hd.le, sub_self]

theorem smoothAnnularWeights_sum {d : ℕ} (a : Ambient d) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (S : Set (Ambient d)) (x : Ambient d) :
    annularSmoothBallCutoff a r hr x + smoothAnnularWeight a r R hr hR x +
      smoothExteriorWeight a R hR S x = S.indicator (fun _ => 1) x := by
  unfold smoothAnnularWeight smoothExteriorWeight
  ring

end

end RieszRectifiability

end OAI
