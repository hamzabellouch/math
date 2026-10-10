import Mathlib
import OAI.Combinatorics.UniformKServer.AnchorRamp

namespace OAI

                                   
section

/-! The signed scalar accounting inequalities for the reference, park and
hidden-key substeps of the retained-anchor potential. -/
noncomputable section
namespace UniformKServer.AnchorScalar
open Finset
open scoped Classical

 theorem reference (r b I M u s C : ℝ) (hr : 0≤r) (hb : 0≤b) (hI : 0≤I)
    (hIM : I≤M) (hu : 0<u) (hs : s=1+M) (hspos : 0<s) (hbC : b≤C*u)
    (hC : 0≤C) : r*b/s*I-r*b/u*I≤r*C*(u+s) := by
  by_cases hsu : u ≤ s
  · have hinv : 1/s≤1/u := one_div_le_one_div_of_le hu hsu
    have hm := mul_le_mul_of_nonneg_left hinv (show 0≤r*b*I by positivity)
    have he : r*b/s*I-r*b/u*I≤0 := by
      have h1 : r*b*I*(1/s)=r*b/s*I := by ring
      have h2 : r*b*I*(1/u)=r*b/u*I := by ring
      rw [h1,h2] at hm
      linarith
    exact he.trans (by positivity)
  · have hIs : I/s≤1 := (div_le_one hspos).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_left hIs (show 0≤r*b by positivity)
    have hz : 0≤r*b/u*I := by positivity
    have hbc := mul_le_mul_of_nonneg_left hbC hr
    have hcs : 0≤r*C*s := by positivity
    have he : r*b*(I/s)=r*b/s*I := by ring
    rw [he] at hm
    nlinarith

theorem parks (r b c I u ρ : ℝ) (hr : 0≤r) (hI : 0≤I) (hu : 0<u)
    (hIu : I≤ρ*u) : |r*c/u*I-r*b/u*I|≤ρ*r*|c-b| := by
  have hb : I/u≤ρ := (div_le_iff₀ hu).mpr hIu
  have he : r*c/u*I-r*b/u*I=r*(c-b)*(I/u) := by ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg (by positivity : 0≤I/u)]
  have hm := mul_le_mul_of_nonneg_left hb (show 0≤r*|c-b| by positivity)
  nlinarith

variable {X H T : Type*} [MetricSpace X]
def value (r : ℝ) (c : H→ℝ) (a : H→X) (l : H⊕T) (p : X) : ℝ :=
  match l with
  | Sum.inl h => c h*AnchorRamp.value r (a h) p
  | Sum.inr _ => 0

theorem value_nonneg (r : ℝ) (c : H→ℝ) (a : H→X) (hc : ∀ h,0≤c h) (l : H⊕T) (p : X) :
    0≤value r c a l p := by
  cases l with
  | inl h => exact mul_nonneg (hc h) (AnchorRamp.value_range r (a h) p).1
  | inr _ => exact le_rfl

theorem value_bound (r C : ℝ) (c : H→ℝ) (a : H→X) (hc : ∀ h,0≤c h)
    (hC : 0≤C) (hcC : ∀ h,c h≤C) (l : H⊕T) (p : X) : value r c a l p≤C := by
  cases l with
  | inl h =>
    exact (mul_le_of_le_one_right (hc h) (AnchorRamp.value_range r (a h) p).2).trans (hcC h)
  | inr _ => exact hC

def near (r : ℝ) (c : H→ℝ) (a : H→X) (l : H⊕T) (p : X) : ℝ :=
  match l with
  | Sum.inl h => if dist (a h) p<7*r then c h else 0
  | Sum.inr _ => 0

theorem near_nonneg (r : ℝ) (c : H→ℝ) (a : H→X) (hc : ∀ h,0≤c h) (l : H⊕T) (p : X) :
    0≤near r c a l p := by
  cases l with
  | inl h => dsimp only [near]; split_ifs; exact hc h; exact le_rfl
  | inr _ => exact le_rfl

theorem member (r C : ℝ) (hr : 0<r) (c : H→ℝ) (a : H→X) (hc : ∀ h,0≤c h)
    (hC : 0≤C) (hcC : ∀ h,c h≤C) (l m : H⊕T) (y z : X) :
    r*(value r c a m z-value r c a l y)≤
      C*r*(if l=m then 0 else 1)+dist y z/3*near r c a l y := by
  by_cases he : l=m
  · subst m
    rw [ite_eq_left rfl,mul_zero,zero_add]
    cases l with
    | inr _ => simp only [value,near,sub_self,mul_zero]; exact le_rfl
    | inl h =>
      have hp := AnchorRamp.change r hr (a h) y z
      have hm := mul_le_mul_of_nonneg_left hp (hc h)
      have hle := mul_le_mul_of_nonneg_left
        (le_max_left (AnchorRamp.value r (a h) z-AnchorRamp.value r (a h) y) 0)
        (mul_nonneg (hc h) hr.le)
      dsimp only [value,near]
      split_ifs with hd
      · rw [ite_eq_left hd] at hm
        nlinarith only [hm,hle]
      · rw [ite_eq_right hd] at hm
        simp only [mul_zero] at hm ⊢
        nlinarith only [hm,hle]
  · rw [ite_eq_right he,mul_one]
    have hm := value_bound r C c a hc hC hcC m z
    have hl := value_nonneg r c a hc l y
    have hnear := near_nonneg r c a hc l y
    have hd : 0≤dist y z/3*near r c a l y := mul_nonneg (by positivity) hnear
    nlinarith

end UniformKServer.AnchorScalar

end


end

end OAI
