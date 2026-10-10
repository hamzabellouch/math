import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleBoundaryLinear
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleRatioSlit

namespace OAI

/-! # Nonvanishing of the Cauchy-kernel integral in the counting rectangle -/

open Set MeasureTheory
namespace DefocusingNLS

theorem zero_mem_countingRectangle (V : ℝ) (hV : 0 < V) :
    (0 : ℂ) ∈ countingRectangle V := by
  change -(1/32 : ℝ) < 0 ∧ (0 : ℝ) < 8 ∧ -V < 0 ∧ (0 : ℝ) < V
  exact ⟨by norm_num, by norm_num, by linarith, hV⟩

theorem countingBoundaryIntegral_inv_im_pos (V : ℝ) (hV : 0 < V) :
    0 < (countingBoundaryIntegral V (fun z => z⁻¹)).im := by
  have hn (z : ℂ) (hz : z ∈ countingRectangleBoundary V) : z ≠ 0 :=
    countingBoundary_ne_interior hz (zero_mem_countingRectangle V hV)
  have hc : ContinuousOn (fun z : ℂ => z⁻¹) (countingRectangleBoundary V) :=
    continuousOn_id.inv₀ hn
  obtain ⟨hb, ht, hr, hl⟩ := countingBoundary_edge_integrable V hV _ hc
  have hbpos (x : ℝ) : 0 < (((x : ℂ) - (V : ℂ) * Complex.I)⁻¹).im := by
    rw [Complex.inv_im]
    have he : ((x : ℂ) - (V : ℂ) * Complex.I).im = -V := by simp
    rw [he, neg_neg]
    apply div_pos hV
    apply Complex.normSq_pos.mpr
    intro heq
    have := congrArg Complex.im heq
    simp only [he, Complex.zero_im] at this
    linarith
  have hbc : ContinuousOn (fun x : ℝ => (((x : ℂ) - (V : ℂ) * Complex.I)⁻¹).im)
      (uIcc (-(1/32 : ℝ)) 8) := by
    apply Complex.continuous_im.comp_continuousOn
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx heq
    have he := congrArg Complex.im heq
    simp at he
    linarith
  have hbi : 0 < (∫ x : ℝ in (-(1/32 : ℝ))..8,
      (((x : ℂ) - (V : ℂ) * Complex.I)⁻¹).im) :=
    intervalIntegral.intervalIntegral_pos_of_pos hbc.intervalIntegrable hbpos (by norm_num)
  have hti : (∫ x : ℝ in (-(1/32 : ℝ))..8,
      (((x : ℂ) + (V : ℂ) * Complex.I)⁻¹).im) ≤ 0 := by
    rw [← neg_nonneg, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    simp only [Complex.inv_im]
    have he : ((x : ℂ) + (V : ℂ) * Complex.I).im = V := by simp
    rw [he, neg_div, neg_neg]
    exact div_nonneg hV.le (Complex.normSq_nonneg _)
  have hri : 0 ≤ (∫ y : ℝ in (-V)..V, ((8 + (y : ℂ) * Complex.I)⁻¹).re) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y hy
    simp only [Complex.inv_re]
    have he : (8 + (y : ℂ) * Complex.I).re = 8 := by simp
    rw [he]
    exact div_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hli : (∫ y : ℝ in (-V)..V, ((-(1/32 : ℂ) + (y : ℂ) * Complex.I)⁻¹).re) ≤ 0 := by
    rw [← neg_nonneg, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y hy
    simp only [Complex.inv_re]
    have he : (-(1/32 : ℂ) + (y : ℂ) * Complex.I).re = -(1/32 : ℝ) := by norm_num
    rw [he, neg_div, neg_neg]
    exact div_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hbEq : (∫ x : ℝ in (-(1/32))..8, ((x : ℂ) - (V : ℂ) * Complex.I)⁻¹).im =
      ∫ x : ℝ in (-(1/32))..8, (((x : ℂ) - (V : ℂ) * Complex.I)⁻¹).im := by
    simpa using! (intervalIntegral.intervalIntegral_im hb).symm
  have htEq : (∫ x : ℝ in (-(1/32))..8, ((x : ℂ) + (V : ℂ) * Complex.I)⁻¹).im =
      ∫ x : ℝ in (-(1/32))..8, (((x : ℂ) + (V : ℂ) * Complex.I)⁻¹).im := by
    simpa using! (intervalIntegral.intervalIntegral_im ht).symm
  have hrEq : (∫ y : ℝ in (-V)..V, (8 + (y : ℂ) * Complex.I)⁻¹).re =
      ∫ y : ℝ in (-V)..V, ((8 + (y : ℂ) * Complex.I)⁻¹).re := by
    simpa using! (intervalIntegral.intervalIntegral_re hr).symm
  have hlEq : (∫ y : ℝ in (-V)..V, (-(1/32 : ℂ) + (y : ℂ) * Complex.I)⁻¹).re =
      ∫ y : ℝ in (-V)..V, ((-(1/32 : ℂ) + (y : ℂ) * Complex.I)⁻¹).re := by
    simpa using! (intervalIntegral.intervalIntegral_re hl).symm
  rw [← hbEq] at hbi
  rw [← htEq] at hti
  rw [← hrEq] at hri
  rw [← hlEq] at hli
  simp only [countingBoundaryIntegral, Complex.sub_im, Complex.add_im, Complex.I_mul_im]
  linarith

theorem countingBoundaryIntegral_inv_ne_zero (V : ℝ) (hV : 0 < V) :
    countingBoundaryIntegral V (fun z => z⁻¹) ≠ 0 := by
  intro he
  have hp := countingBoundaryIntegral_inv_im_pos V hV
  simp [he] at hp

end DefocusingNLS

end OAI
