import OAI.Geometry.RCD.Metric.TranslatedDensityLaw

namespace OAI

/-! # Translation moves a difference quotient onto its compact test -/

open MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem compact_difference_pairing {n : ℕ} {f ψ : Euclidean n → ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hs : HasCompactSupport ψ)
    (h : Euclidean n) (t : ℝ) :
    (∫ x, ((f (x+h)-f x)/t)*ψ x)=
      ∫ x, f x*((ψ (x-h)-ψ x)/t) := by
  have hi0 : Integrable (fun x => f x*ψ x) volume :=
    (hf.mul hψ).integrable_of_hasCompactSupport hs.mul_left
  have hi1 : Integrable (fun x => f (x+h)*ψ x) volume :=
    ((hf.comp (by fun_prop)).mul hψ).integrable_of_hasCompactSupport hs.mul_left
  have hshift : HasCompactSupport (fun x => ψ (x-h)) := by
    simpa only [Function.comp_def,Homeomorph.coe_addRight,sub_eq_add_neg] using
      hs.comp_homeomorph (Homeomorph.addRight (-h))
  have hi2 : Integrable (fun x => f x*ψ (x-h)) volume :=
    (hf.mul (hψ.comp (by fun_prop))).integrable_of_hasCompactSupport hshift.mul_left
  have he : (∫ x, f (x+h)*ψ x)=(∫ x, f x*ψ (x-h)) := by
    calc
      (∫ x, f (x+h)*ψ x) = (∫ x, f ((x-h)+h)*ψ (x-h)) :=
        (integral_sub_right_eq_self (fun x => f (x+h)*ψ x) h).symm
      _ = _ := by simp only [sub_add_cancel]
  have hleft : (fun x => ((f (x+h)-f x)/t)*ψ x)=
      fun x => t⁻¹*(f (x+h)*ψ x-f x*ψ x) := by funext x; ring
  have hright : (fun x => f x*((ψ (x-h)-ψ x)/t))=
      fun x => t⁻¹*(f x*ψ (x-h)-f x*ψ x) := by funext x; ring
  rw [hleft,hright,integral_const_mul,integral_const_mul,
    integral_sub hi1 hi0,integral_sub hi2 hi0,he]

end RegularPointCoordinates

end

end OAI
