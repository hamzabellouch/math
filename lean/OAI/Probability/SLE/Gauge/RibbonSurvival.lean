import OAI.Probability.SLE.Geometry.GuideTube
import OAI.Probability.SLE.NearRealContraction

namespace OAI

/-! Actual surviving-component assertions for access rays and the splice.
Containment of the past in the initial rectangle implies that every point
above or beside it belongs to the unbounded surviving component. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem survives_of_unbounded_free_curve
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (α : ℝ≥0 → ℂ) (hα : Continuous α)
    (hfree : range α ⊆ upperHalfPlane \ (γ '' Icc 0 T))
    (hunbounded : ¬ Bornology.IsBounded (range α)) :
    range α ⊆ survivingDomain γ T := by
  rintro z ⟨u, rfl⟩
  refine ⟨hfree (mem_range_self u), ?_⟩
  intro hb
  apply hunbounded
  exact hb.subset ((isPreconnected_range hα).subset_connectedComponentIn
    (mem_range_self u) hfree)

def upwardRay (z : ℂ) (u : ℝ≥0) : ℂ := z + (u : ℝ) * Complex.I

theorem upwardRay_continuous (z : ℂ) : Continuous (upwardRay z) :=
  continuous_const.add ((Complex.continuous_ofReal.comp NNReal.continuous_coe).mul continuous_const)

theorem upwardRay_unbounded (z : ℂ) : ¬ Bornology.IsBounded (range (upwardRay z)) := by
  intro hb
  obtain ⟨R, hR, hbound⟩ := hb.exists_pos_norm_lt
  let u : ℝ≥0 := ⟨R + |z.im| + 1, by positivity⟩
  have hu := hbound (upwardRay z u) (mem_range_self u)
  have hi := Complex.im_le_norm (upwardRay z u)
  simp only [upwardRay, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hi
  change z.im + (R + |z.im| + 1) ≤ ‖upwardRay z u‖ at hi
  linarith [neg_le_abs z.im]

theorem outside_initial_rectangle_survives
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (B : ℝ)
    (hpast : γ '' Icc 0 T ⊆ GuideSplice.closedInitialRectangle B) :
    upperHalfPlane \ GuideSplice.closedInitialRectangle B ⊆ survivingDomain γ T := by
  intro z hz
  have hfree : range (upwardRay z) ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    rintro w ⟨u, rfl⟩
    have him : (upwardRay z u).im = z.im + (u : ℝ) := by simp [upwardRay]
    have hre : (upwardRay z u).re = z.re := by simp [upwardRay]
    refine ⟨by change 0 < (upwardRay z u).im; rw [him]; exact add_pos_of_pos_of_nonneg hz.1 u.coe_nonneg, ?_⟩
    intro hp
    have hrect := hpast hp
    change |(upwardRay z u).re| ≤ B / 16 ∧
      0 ≤ (upwardRay z u).im ∧ (upwardRay z u).im ≤ B / 4 at hrect
    apply hz.2
    change |z.re| ≤ B / 16 ∧ 0 ≤ z.im ∧ z.im ≤ B / 4
    refine ⟨by simpa only [hre] using hrect.1, hz.1.le, ?_⟩
    rw [him] at hrect
    linarith [u.coe_nonneg, hrect.2.2]
  have hs := survives_of_unbounded_free_curve γ T (upwardRay z)
    (upwardRay_continuous z) hfree (upwardRay_unbounded z) (mem_range_self 0)
  simpa only [upwardRay, NNReal.coe_zero, Complex.ofReal_zero, zero_mul, add_zero] using hs

/-- The open continuation tube avoids the actual filled hull whenever the
past lies in the containing rectangle; no filled-hull containment is assumed. -/
theorem continuationTube_subset_survivingDomain
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (B : ℝ)
    (hpast : γ '' Icc 0 T ⊆ GuideSplice.closedInitialRectangle B)
    (F : ℂ → ℂ) (a : ℂ) (r : ℝ) (O : Set ℂ) :
    GuideSplice.continuationTube F a r B O ⊆ survivingDomain γ T := by
  intro z hz
  exact outside_initial_rectangle_survives γ T B hpast ⟨hz.1.1, hz.2⟩

end SLEExactGauge

end

end OAI
