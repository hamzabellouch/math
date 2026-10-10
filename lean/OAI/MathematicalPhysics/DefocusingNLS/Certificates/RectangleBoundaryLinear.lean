import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleBoundaryPrimitive

namespace OAI

/-! # Linearity and locality of the rectangular contour integral -/

open Set MeasureTheory
namespace DefocusingNLS

theorem countingBoundary_edge_integrable (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : ContinuousOn f (countingRectangleBoundary V)) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (V : ℂ) * Complex.I)) volume (-(1/32)) 8 ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (V : ℂ) * Complex.I)) volume (-(1/32)) 8 ∧
    IntervalIntegrable (fun y : ℝ => f (8 + (y : ℂ) * Complex.I)) volume (-V) V ∧
    IntervalIntegrable (fun y : ℝ => f (-(1/32 : ℂ) + (y : ℂ) * Complex.I)) volume (-V) V := by
  have hh (y : ℝ) (hy : y = -V ∨ y = V) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) volume (-(1/32)) 8 := by
    apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun x hx => horizontal_mem_countingBoundary V y x hV hy hx)
  have hv (x : ℝ) (hx : x = -(1/32 : ℝ) ∨ x = 8) :
      IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) volume (-V) V := by
    apply ContinuousOn.intervalIntegrable
    exact hf.comp (by fun_prop) (fun y hy => vertical_mem_countingBoundary V x y hV hx hy)
  refine ⟨?_, hh V (Or.inr rfl), ?_, ?_⟩
  · simpa [sub_eq_add_neg] using hh (-V) (Or.inl rfl)
  · simpa using hv 8 (Or.inr rfl)
  · simpa using hv (-(1/32)) (Or.inl rfl)

theorem countingBoundaryIntegral_congr (V : ℝ) (hV : 0 < V) {f g : ℂ → ℂ}
    (he : EqOn f g (countingRectangleBoundary V)) :
    countingBoundaryIntegral V f = countingBoundaryIntegral V g := by
  have hh (y : ℝ) (hy : y = -V ∨ y = V) :
      (∫ x : ℝ in (-(1/32))..8, f ((x : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ x : ℝ in (-(1/32))..8, g ((x : ℂ) + (y : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact he (horizontal_mem_countingBoundary V y x hV hy hx)
  have hv (x : ℝ) (hx : x = -(1/32 : ℝ) ∨ x = 8) :
      (∫ y : ℝ in (-V)..V, f ((x : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in (-V)..V, g ((x : ℂ) + (y : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact he (vertical_mem_countingBoundary V x y hV hx hy)
  have hb := hh (-V) (Or.inl rfl)
  have hr := hv 8 (Or.inr rfl)
  have hl := hv (-(1/32)) (Or.inl rfl)
  simp only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] at hb
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_one] at hr hl
  unfold countingBoundaryIntegral
  rw [hb, hh V (Or.inr rfl), hr, hl]

theorem countingBoundaryIntegral_sub (V : ℝ) (hV : 0 < V) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (countingRectangleBoundary V))
    (hg : ContinuousOn g (countingRectangleBoundary V)) :
    countingBoundaryIntegral V (fun z => f z - g z) =
      countingBoundaryIntegral V f - countingBoundaryIntegral V g := by
  obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := countingBoundary_edge_integrable V hV f hf
  obtain ⟨hg₁, hg₂, hg₃, hg₄⟩ := countingBoundary_edge_integrable V hV g hg
  simp only [countingBoundaryIntegral, intervalIntegral.integral_sub hf₁ hg₁,
    intervalIntegral.integral_sub hf₂ hg₂, intervalIntegral.integral_sub hf₃ hg₃,
    intervalIntegral.integral_sub hf₄ hg₄]
  ring

theorem countingBoundaryIntegral_add (V : ℝ) (hV : 0 < V) (f g : ℂ → ℂ)
    (hf : ContinuousOn f (countingRectangleBoundary V))
    (hg : ContinuousOn g (countingRectangleBoundary V)) :
    countingBoundaryIntegral V (fun z => f z + g z) =
      countingBoundaryIntegral V f + countingBoundaryIntegral V g := by
  obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := countingBoundary_edge_integrable V hV f hf
  obtain ⟨hg₁, hg₂, hg₃, hg₄⟩ := countingBoundary_edge_integrable V hV g hg
  simp only [countingBoundaryIntegral, intervalIntegral.integral_add hf₁ hg₁,
    intervalIntegral.integral_add hf₂ hg₂, intervalIntegral.integral_add hf₃ hg₃,
    intervalIntegral.integral_add hf₄ hg₄]
  ring

theorem countingBoundaryIntegral_const_mul (V : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    countingBoundaryIntegral V (fun z => c * f z) = c * countingBoundaryIntegral V f := by
  simp only [countingBoundaryIntegral, intervalIntegral.integral_const_mul]
  ring

@[simp] theorem countingBoundaryIntegral_zero (V : ℝ) :
    countingBoundaryIntegral V (fun _ => 0) = 0 := by simp [countingBoundaryIntegral]

end DefocusingNLS

end OAI
