import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

/-! The two first integrals of the twelve-dimensional radial harmonic equation. -/

open Set
namespace DefocusingNLS

theorem spectralRadialPower_hasDerivAt (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun r : ℝ => (r : ℂ)^n) ((n : ℂ)*(x : ℂ)^n/(x : ℂ)) x := by
  have h := ((hasDerivAt_id x).ofReal_comp).pow n
  apply h.congr_deriv
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,id_eq,Complex.ofReal_one,mul_one]
              rw [pow_succ]
              field_simp

noncomputable def spectralEulerGrowing (n : ℕ) (g P : ℝ → ℂ) (r : ℝ) : ℂ :=
  (P r/(r : ℂ)^10+((n : ℂ)+10)*g r)/(r : ℂ)^n

noncomputable def spectralEulerSingular (n : ℕ) (g P : ℝ → ℂ) (r : ℝ) : ℂ :=
  (r : ℂ)^(n+10)*((n : ℂ)*g r-P r/(r : ℂ)^10)

theorem spectralEuler_invariant_derivatives (n : ℕ) (g P : ℝ → ℂ) (x : ℝ)
    (hx : x ≠ 0)
    (hg : HasDerivAt g (P x/(x : ℂ)^11) x)
    (hP : HasDerivAt P ((n : ℂ)*((n : ℂ)+10)*(x : ℂ)^9*g x) x) :
    HasDerivAt (spectralEulerGrowing n g P) 0 x ∧
      HasDerivAt (spectralEulerSingular n g P) 0 x := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have h10 := spectralRadialPower_hasDerivAt 10 x hx
  have hp := hP.div h10 (pow_ne_zero _ hx')
  have hplus : HasDerivAt (fun r : ℝ => P r/(r : ℂ)^10+((n : ℂ)+10)*g r)
      ((n : ℂ)*(P x/(x : ℂ)^10+((n : ℂ)+10)*g x)/(x : ℂ)) x := by
    apply (hp.add (hg.const_mul ((n : ℂ)+10))).congr_deriv
    push_cast
    field_simp
    ring
  have hminus : HasDerivAt (fun r : ℝ => (n : ℂ)*g r-P r/(r : ℂ)^10)
      (-((n : ℂ)+10)*((n : ℂ)*g x-P x/(x : ℂ)^10)/(x : ℂ)) x := by
    apply ((hg.const_mul (n : ℂ)).sub hp).congr_deriv
    push_cast
    field_simp
    ring
  constructor
  · apply (hplus.div (spectralRadialPower_hasDerivAt n x hx) (pow_ne_zero _ hx')).congr_deriv
    field_simp
    ring
  · apply ((spectralRadialPower_hasDerivAt (n+10) x hx).mul hminus).congr_deriv
    push_cast
    field_simp
    ring

theorem spectralEuler_invariants_constant (n : ℕ) (L : ℝ) (g P : ℝ → ℂ)
    (hg : ∀ x ∈ Ioo 0 L, HasDerivAt g (P x/(x : ℂ)^11) x)
    (hP : ∀ x ∈ Ioo 0 L,
      HasDerivAt P ((n : ℂ)*((n : ℂ)+10)*(x : ℂ)^9*g x) x)
    (x y : ℝ) (hx : x ∈ Ioo 0 L) (hy : y ∈ Ioo 0 L) :
    spectralEulerGrowing n g P x=spectralEulerGrowing n g P y ∧
      spectralEulerSingular n g P x=spectralEulerSingular n g P y := by
  have hd (r : ℝ) (hr : r ∈ Ioo 0 L) :=
    spectralEuler_invariant_derivatives n g P r hr.1.ne' (hg r hr) (hP r hr)
  constructor
  · exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) L).isPreconnected
      (fun r hr => (hd r hr).1.differentiableAt.differentiableWithinAt)
      (fun r hr => (hd r hr).1.deriv) hx hy
  · exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) L).isPreconnected
      (fun r hr => (hd r hr).2.differentiableAt.differentiableWithinAt)
      (fun r hr => (hd r hr).2.deriv) hx hy

end DefocusingNLS

end OAI
