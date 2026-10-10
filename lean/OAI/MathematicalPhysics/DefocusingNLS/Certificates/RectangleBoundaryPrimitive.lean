import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleBoundaryIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.SegmentInversePrimitive

namespace OAI

/-! # Integrating derivatives on the spectral rectangle -/

open Set MeasureTheory
namespace DefocusingNLS

theorem integral_segment_deriv (f : ℂ → ℂ) (u v : ℂ) (l r : ℝ)
    (hf : ∀ t ∈ uIcc l r, AnalyticAt ℂ f (u + (t : ℂ) * v)) :
    (∫ t : ℝ in l..r, v * deriv f (u + (t : ℂ) * v)) =
      f (u + (r : ℂ) * v) - f (u + (l : ℂ) * v) := by
  have hd (t : ℝ) (ht : t ∈ uIcc l r) :
      HasDerivAt (fun s : ℝ => f (u + (s : ℂ) * v))
        (v * deriv f (u + (t : ℂ) * v)) t := by
    simpa only [Function.comp_def, smul_eq_mul, id_eq, Complex.ofReal_one, one_mul] using!
      (hf t ht).differentiableAt.hasDerivAt.scomp t
        (((hasDerivAt_id t).ofReal_comp.mul_const v).const_add u)
  have hi : IntervalIntegrable (fun t : ℝ => v * deriv f (u + (t : ℂ) * v))
      volume l r := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    intro t ht
    have hp : ContinuousAt (fun s : ℝ => u + (s : ℂ) * v) t := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (f := fun s : ℝ => u + (s : ℂ) * v)
        (g := deriv f) (hf t ht).deriv.continuousAt hp)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

theorem horizontal_mem_countingBoundary (V y x : ℝ) (hV : 0 < V)
    (hy : y = -V ∨ y = V) (hx : x ∈ uIcc (-(1/32 : ℝ)) 8) :
    (x : ℂ) + (y : ℂ) * Complex.I ∈ countingRectangleBoundary V := by
  rw [uIcc_of_le (by norm_num : -(1/32 : ℝ) ≤ 8)] at hx
  rw [mem_countingRectangleBoundary_iff]
  simp only [closedCountingRectangle, mem_ofPred_eq,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rcases hy with rfl | rfl <;>
    exact ⟨⟨hx.1, hx.2, by linarith, by linarith⟩, by tauto⟩

theorem vertical_mem_countingBoundary (V x y : ℝ) (hV : 0 < V)
    (hx : x = -(1/32 : ℝ) ∨ x = 8) (hy : y ∈ uIcc (-V) V) :
    (x : ℂ) + (y : ℂ) * Complex.I ∈ countingRectangleBoundary V := by
  rw [uIcc_of_le (by linarith : -V ≤ V)] at hy
  rw [mem_countingRectangleBoundary_iff]
  simp only [closedCountingRectangle, mem_ofPred_eq,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rcases hx with rfl | rfl <;>
    exact ⟨⟨by norm_num, by norm_num, hy.1, hy.2⟩, by tauto⟩

theorem countingBoundaryIntegral_deriv (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (countingRectangleBoundary V)) :
    countingBoundaryIntegral V (deriv f) = 0 := by
  have hb := integral_segment_deriv f (-(V : ℂ) * Complex.I) 1 (-(1/32 : ℝ)) 8
    (fun t ht => by simpa [mul_one, add_comm, neg_mul, sub_eq_add_neg] using
      (hf _ (horizontal_mem_countingBoundary V (-V) t hV (Or.inl rfl) ht)))
  have ht := integral_segment_deriv f ((V : ℂ) * Complex.I) 1 (-(1/32 : ℝ)) 8
    (fun t ht => by simpa [mul_one, add_comm] using
      (hf _ (horizontal_mem_countingBoundary V V t hV (Or.inr rfl) ht)))
  have hr := integral_segment_deriv f 8 Complex.I (-V) V
    (fun t ht => hf _ (vertical_mem_countingBoundary V 8 t hV (Or.inr rfl) ht))
  have hl := integral_segment_deriv f (-(1/32 : ℂ)) Complex.I (-V) V
    (fun t ht => by simpa using
      (hf _ (vertical_mem_countingBoundary V (-(1/32 : ℝ)) t hV (Or.inl rfl) ht)))
  simp only [mul_one, one_mul] at hb ht
  simp only [add_comm ((V : ℂ) * Complex.I)] at ht
  rw [intervalIntegral.integral_const_mul] at hr hl
  simp only [countingBoundaryIntegral]
  have hb' : (∫ x : ℝ in (-(1/32 : ℝ))..8, deriv f ((x : ℂ) - (V : ℂ) * Complex.I)) =
      f (8 - (V : ℂ) * Complex.I) - f (-(1/32 : ℂ) - (V : ℂ) * Complex.I) := by
    simpa [add_comm, neg_mul, sub_eq_add_neg] using hb
  rw [hb', ht, hr, hl]
  simp only [Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_div,
    Complex.ofReal_one, neg_mul, sub_eq_add_neg]
  ring

end DefocusingNLS

end OAI
