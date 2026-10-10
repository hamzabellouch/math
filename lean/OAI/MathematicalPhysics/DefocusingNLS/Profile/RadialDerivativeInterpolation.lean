import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! A short-interval derivative estimate used to differentiate outgoing remainders. -/

open Set
namespace DefocusingNLS

theorem radial_derivative_interpolation (f : ℝ → ℂ) (t h A B : ℝ)
    (hh : 0 < h) (hB : 0 ≤ B)
    (hf : ∀ s ∈ Icc t (t+h), DifferentiableAt ℝ f s)
    (hdf : ∀ s ∈ Icc t (t+h), DifferentiableAt ℝ (deriv f) s)
    (hA : ∀ s ∈ Icc t (t+h), ‖f s‖ ≤ A)
    (hdd : ∀ s ∈ Icc t (t+h), ‖deriv (deriv f) s‖ ≤ B) :
    ‖deriv f t‖ ≤ 2*A/h+B*h := by
  have ht : t ∈ Icc t (t+h) := ⟨le_rfl,by linarith⟩
  have hth : t+h ∈ Icc t (t+h) := ⟨by linarith,le_rfl⟩
  have hLip (s : ℝ) (hs : s ∈ Icc t (t+h)) :
      ‖deriv f s-deriv f t‖ ≤ B*h := by
    have hb := Convex.norm_image_sub_le_of_norm_deriv_le hdf hdd
      (convex_Icc t (t+h)) ht hs
    have hn : ‖s-t‖ ≤ h := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith [hs.2]
    exact hb.trans (mul_le_mul_of_nonneg_left hn hB)
  let g : ℝ → ℂ := fun s => f s-f t-((s-t : ℝ) : ℂ)*deriv f t
  have hg (s : ℝ) (hs : s ∈ Icc t (t+h)) :
      HasDerivAt g (deriv f s-deriv f t) s := by
    have hh := ((hf s hs).hasDerivAt.sub_const (f t)).sub
      (((hasDerivAt_id s).sub_const t).ofReal_comp.mul_const (deriv f t))
    convert hh using 1 <;> simp [g,funext_iff]
  have hrem := (convex_Icc t (t+h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hg s hs).hasDerivWithinAt) hLip ht hth
  have hgnorm : ‖g (t+h)‖ ≤ B*h^2 := by
    simpa only [g,sub_self,Complex.ofReal_zero,zero_mul,sub_zero,add_sub_cancel_left,
      Real.norm_eq_abs,abs_of_pos hh,mul_assoc,pow_two] using hrem
  have hidentity : (h : ℂ)*deriv f t=f (t+h)-f t-g (t+h) := by
    dsimp [g]
    push_cast
    ring
  have hbound : h*‖deriv f t‖ ≤ 2*A+B*h^2 := by
    calc
      h*‖deriv f t‖ = ‖(h : ℂ)*deriv f t‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
      _ = ‖f (t+h)-f t-g (t+h)‖ := congrArg norm hidentity
      _ ≤ ‖f (t+h)‖+‖f t‖+‖g (t+h)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
      _ ≤ A+A+B*h^2 := add_le_add (add_le_add (hA _ hth) (hA _ ht)) hgnorm
      _ = _ := by ring
  have hcancel : (2*A/h)*h=2*A := div_mul_cancel₀ _ hh.ne'
  nlinarith

end DefocusingNLS

end OAI
