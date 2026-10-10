import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceWeightedQuadrature

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeStopGeometry

open NumberTheoryLean.ReferenceAdmission

def sourceHeight (x : ℝ) : ℝ := max (2*x) (x+2)

theorem sourceHeight_mono {x y : ℝ} (hxy : x ≤ y) : sourceHeight x ≤ sourceHeight y := by
  exact max_le_max (by linarith) (by linarith)

theorem sourceHeight_error {x y d : ℝ} (hxy : |x-y| ≤ d) : sourceHeight x ≤ sourceHeight y+2*d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans hxy
  apply max_le
  · have hy := le_max_left (2*y) (y+2)
    change 2*y ≤ sourceHeight y at hy
    linarith [(abs_le.mp hxy).2]
  · have hy := le_max_right (2*y) (y+2)
    change y+2 ≤ sourceHeight y at hy
    linarith [(abs_le.mp hxy).2]

theorem sourceHeight_lipschitz (x y : ℝ) : |sourceHeight x-sourceHeight y| ≤ 2*|x-y| := by
  have hxy := sourceHeight_error (x:=x) (y:=y) (le_rfl : |x-y| ≤ |x-y|)
  have hyx := sourceHeight_error (x:=y) (y:=x) (le_rfl : |y-x| ≤ |y-x|)
  rw [abs_sub_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem representative_safety_admits {r rrep x xrep Delta : ℝ}
    (hDelta : 0 ≤ Delta) (hx : x ≤ xrep) (hr : rrep ≤ r)
    (hsafe : sourceHeight xrep+3*Delta ≤ rrep) : sourceHeight x ≤ r := by
  have hH := sourceHeight_mono hx
  linarith

theorem regular_margin_to_representative {r rrep x xrep Delta h : ℝ}
    (hr : |rrep-r| ≤ Delta) (hx : |xrep-x| ≤ h)
    (hsmall : 2*h ≤ 6*Delta) (hmargin : sourceHeight x+10*Delta < r) :
    sourceHeight xrep+3*Delta < rrep := by
  have hH := sourceHeight_error hx
  linarith [(abs_le.mp hr).1]

theorem representative_to_actual_window {b₀ b₁ r rrep x xrep Delta h : ℝ}
    (hx : 0 < x) (hxr : x ≤ xrep) (hxh : xrep ≤ x+h)
    (hr : rrep ≤ r) (hrD : r ≤ rrep+Delta)
    (hb₀ : b₀ ≤ xrep) (hb₁ : xrep ≤ b₁)
    (hs₀ : 206/100 ≤ rrep/xrep) (hs₁ : rrep/xrep ≤ 216/100)
    (hsmall : Delta+(218/100)*h ≤ (2/100)*b₀) :
    b₀-h ≤ x ∧ x ≤ b₁ ∧ 204/100 ≤ r/x ∧ r/x ≤ 218/100 := by
  have hxp : 0 < xrep := hx.trans_le hxr
  have hlow := (le_div_iff₀ hxp).mp hs₀
  have hhigh := (div_le_iff₀ hxp).mp hs₁
  refine ⟨by linarith,hxr.trans hb₁,?_,?_⟩
  · apply (le_div_iff₀ hx).mpr
    nlinarith
  · apply (div_le_iff₀ hx).mpr
    nlinarith

theorem actual_mark_to_representative_window {b₀ b₁ r rrep x xrep Delta h : ℝ}
    (hb₀ : 0 < b₀) (hx₀ : 2*b₀ ≤ x) (hx₁ : x ≤ b₁/2)
    (hxr : x ≤ xrep) (hxh : xrep ≤ x+h)
    (hr : rrep ≤ r) (hrD : r ≤ rrep+Delta)
    (hs₀ : 208/100 ≤ r/x) (hs₁ : r/x ≤ 214/100)
    (hh : h ≤ b₀) (hsmall : Delta+(206/100)*h ≤ (4/100)*b₀) :
    b₀ ≤ xrep ∧ xrep ≤ b₁ ∧ 206/100 ≤ rrep/xrep ∧ rrep/xrep ≤ 216/100 := by
  have hx : 0 < x := by linarith
  have hxp : 0 < xrep := hx.trans_le hxr
  have hlow := (le_div_iff₀ hx).mp hs₀
  have hhigh := (div_le_iff₀ hx).mp hs₁
  refine ⟨by linarith,by linarith,?_,?_⟩
  · apply (le_div_iff₀ hxp).mpr
    nlinarith
  · apply (div_le_iff₀ hxp).mpr
    nlinarith

end NumberTheoryLean.RepresentativeStopGeometry

end

end Erdos970

end OAI
