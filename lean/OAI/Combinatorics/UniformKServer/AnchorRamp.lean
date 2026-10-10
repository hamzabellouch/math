import Mathlib
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

                                 
section

/-! Exact clipped ramp and retained-heavy-anchor release. All integrals here
are finite weighted sums on the original finite metric. -/
noncomputable section
namespace UniformKServer.AnchorRamp
open Finset
open scoped Classical

def ramp (u : ℝ) : ℝ := max 0 (min 1 ((u-4)/3))

theorem range (u : ℝ) : ramp u ∈ Set.Icc 0 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem zero (u : ℝ) (hu : u ≤ 4) : ramp u=0 := by
  unfold ramp
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

theorem one (u : ℝ) (hu : 7 ≤ u) : ramp u=1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

theorem lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ |u-v|/3 := by
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min 1 ((u-4)/3)) 0 (min 1 ((v-4)/3))
  have hmin := abs_min_sub_min_le_max (1:ℝ) ((u-4)/3) 1 ((v-4)/3)
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 ((u-4)/3)-min 1 ((v-4)/3)))] at hmax
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg ((u-4)/3-(v-4)/3))] at hmin
  have he : |(u-4)/3-(v-4)/3|=|u-v|/3 := by rw [←sub_div,show (u-4)-(v-4)=u-v by ring,abs_div]; norm_num
  rw [he] at hmin
  exact hmax.trans hmin

variable {X : Type*} [MetricSpace X]

def value (r : ℝ) (a z : X) : ℝ := ramp (dist a z/r)

theorem value_range (r : ℝ) (a z : X) : value r a z ∈ Set.Icc 0 1 := range _

theorem change (r : ℝ) (hr : 0 < r) (a y z : X) :
    r*max (value r a z-value r a y) 0 ≤
      if dist a y < 7*r then dist y z/3 else 0 := by
  by_cases hy : dist a y < 7*r
  · rw [ite_eq_left hy]
    have hL := lipschitz (dist a z/r) (dist a y/r)
    have hd : |dist a z-dist a y| ≤ dist y z := by
      simpa only [dist_comm] using abs_dist_sub_le z y a
    have hd' : |dist a z/r-dist a y/r| ≤ dist y z/r := by
      rw [←sub_div,abs_div,abs_of_pos hr]
      exact div_le_div_of_nonneg_right hd hr.le
    have h : value r a z-value r a y ≤ dist y z/r/3 := by
      exact (le_abs_self _).trans (hL.trans (div_le_div_of_nonneg_right hd' (by norm_num)))
    have hm : max (value r a z-value r a y) 0 ≤ dist y z/r/3 :=
      max_le h (by positivity)
    have hh := mul_le_mul_of_nonneg_left hm hr.le
    calc
      _ ≤ r*(dist y z/r/3) := hh
      _ = _ := by field_simp
  · rw [ite_eq_right hy]
    have ho : value r a y=1 := one _ ((le_div_iff₀ hr).2 (by linarith))
    rw [ho,max_eq_right (by linarith [(value_range r a z).2]),mul_zero]

variable [Fintype X]

def ball (x : X) (R : ℝ) : Finset X := univ.filter (fun z => dist x z ≤ R)
def mass (μ : X → ℝ) (C : Finset X) : ℝ := ∑ z ∈ C, μ z

omit [Fintype X] in
theorem inner_change (r γ : ℝ) (hr : 0 < r) (hγ : γ < 1) (a x z : X)
    (ha : 8*r < dist a x) (hz : dist x z ≤ γ*r) : value r x z-value r a z = -1 := by
  have hn : value r x z=0 := zero _ ((div_le_iff₀ hr).2 (by nlinarith))
  have hp : value r a z=1 := by
    apply one
    apply (le_div_iff₀ hr).2
    have ht := dist_triangle a z x
    rw [dist_comm z x] at ht
    nlinarith
  rw [hn,hp]
  norm_num

theorem integral_drop (μ : X → ℝ) (hμ : ∀ z, 0 ≤ μ z) (C : Finset X)
    (r γ δ : ℝ) (hr : 0 < r) (hγ : γ < 1) (a x : X)
    (ha : 8*r < dist a x) (hC : ball x (γ*r) ⊆ C)
    (hm : mass μ C ≤ (1+δ)*mass μ (ball x (γ*r))) :
    (∑ z ∈ C, μ z*(value r x z-value r a z)) ≤ -(1-δ)*mass μ (ball x (γ*r)) := by
  have hp (z : X) : value r x z-value r a z ≤ if z ∈ ball x (γ*r) then -1 else 1 := by
    by_cases hz : z ∈ ball x (γ*r)
    · rw [ite_eq_left hz]
      exact (inner_change r γ hr hγ a x z ha (mem_filter.mp hz).2).le
    · rw [ite_eq_right hz]
      linarith [(value_range r x z).2,(value_range r a z).1]
  have hs := sum_le_sum (fun z (_ : z ∈ C) => mul_le_mul_of_nonneg_left (hp z) (hμ z))
  have he : (∑ z ∈ C, μ z*(if z ∈ ball x (γ*r) then -1 else 1))=
      mass μ C-2*mass μ (ball x (γ*r)) := by
    have ht (z : X) : μ z*(if z ∈ ball x (γ*r) then -1 else 1)=μ z-2*(if z ∈ ball x (γ*r) then μ z else 0) := by
      split_ifs <;> ring
    simp_rw [ht]
    rw [sum_sub_distrib,←mul_sum,←sum_filter]
    congr 2
    rw [filter_mem_eq_inter,inter_eq_right.mpr hC]
    rfl
  rw [he] at hs
  nlinarith

theorem payment (r b d H I δ : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b) (hd : 0 < d)
    (hH : 0 ≤ H) (hδ : δ ≤ 1/100) (hden : d ≤ (6/5)*(2+δ)*H)
    (hI : I ≤ -(1-δ)*H) : r*b/d*I ≤ -(1/4)*r*b := by
  have hm := mul_le_mul_of_nonneg_left hI (show 0 ≤ r*b/d by positivity)
  have hc : d/4 ≤ (1-δ)*H := by nlinarith [mul_nonneg (show 0 ≤ 1/100-δ by linarith) hH]
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ r*b/d by positivity)
  have he : r*b/d*(d/4)=r*b/4 := by field_simp
  rw [he] at hh
  nlinarith

end UniformKServer.AnchorRamp

end


end

end OAI
