import Mathlib
import OAI.Combinatorics.KMedian.Process.Taper
import OAI.Combinatorics.KMedian.Geometry.RationalBrackets

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

theorem marginal_piecewise {P d r : ℝ} (hP : 0 < P) :
    marginal P d r=if r*d ≤ 1-P then 1 else
      if 1 ≤ r*d then 0 else (1-r*d)/P := by
  split_ifs with hs hz
  · exact marginal_one hP hs
  · exact marginal_zero hz
  · have hp : 0 ≤ 1-r*d := by linarith
    have hh : (1-r*d)/P ≤ 1 := (div_le_one₀ hP).mpr (by linarith)
    exact (congrArg (min 1) (congrArg (fun a => a/P) (max_eq_left hp))).trans (min_eq_right hh)

def aCoef (P d t : ℚ) : ℚ := if t*d ≤ 1-P then 1 else if 1 ≤ t*d then 0 else 1/P

def bCoef (P d t : ℚ) : ℚ := if t*d ≤ 1-P then 0 else if 1 ≤ t*d then 0 else d/P

theorem marginal_affine {P d t : ℚ} {x : ℝ} (hP : 0 < (P:ℝ))
    (ha : (x*(d:ℝ) ≤ 1-(P:ℝ) ↔ t*d ≤ 1-P))
    (hb : (1 ≤ x*(d:ℝ) ↔ 1 ≤ t*d)) :
    marginal P d x=(aCoef P d t:ℝ)-x*(bCoef P d t:ℝ) := by
  rw [marginal_piecewise hP]
  by_cases hs : t*d ≤ 1-P
  · rw [ite_eq_left (ha.mpr hs)]
    simp only [aCoef,bCoef,ite_eq_left hs,Rat.cast_one,Rat.cast_zero,mul_zero,sub_zero]
  · rw [ite_eq_right (fun he => hs (ha.mp he))]
    by_cases hz : 1 ≤ t*d
    · rw [ite_eq_left (hb.mpr hz)]
      simp only [aCoef,bCoef,ite_eq_right hs,ite_eq_left hz,Rat.cast_zero,mul_zero,sub_zero]
    · rw [ite_eq_right (fun he => hz (hb.mp he))]
      simp only [aCoef,bCoef,ite_eq_right hs,ite_eq_right hz,Rat.cast_div,Rat.cast_one]
      ring

variable {I : Type*} [Fintype I]

def upper (d : I → ℚ) : ℚ := 1+∑ i, (d i)⁻¹

def breakpoints (P : ℚ) (d : I → ℚ) : Finset ℚ :=
  insert 0 (insert (upper d) ((univ.image (fun i => (1-P)/d i)) ∪ (univ.image (fun i => 1/d i))))

def A (P : ℚ) (d : I → ℚ) (t : ℚ) : ℚ := ∑ i, aCoef P (d i) t

def B (P : ℚ) (d : I → ℚ) (t : ℚ) : ℚ := ∑ i, bCoef P (d i) t

theorem mass_affine {P g t : ℚ} {d : I → ℚ} {x : ℝ} (hP : 0 < (P:ℝ))
    (ha : ∀ i, (x*(d i:ℝ) ≤ 1-(P:ℝ) ↔ t*d i ≤ 1-P))
    (hb : ∀ i, (1 ≤ x*(d i:ℝ) ↔ 1 ≤ t*d i)) :
    mass g P (fun i => (d i:ℝ)) x=(g:ℝ)*((A P d t:ℝ)-x*(B P d t:ℝ)) := by
  simp only [mass,marginal_affine hP (ha _) (hb _),A,B,Rat.cast_sum]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]

theorem cuts_in_interval {P : ℚ} {d : I → ℚ} (hd : ∀ i, 0 ≤ d i) (hP : P < 1)
    (a b t : ℚ) (hgap : ∀ q ∈ breakpoints P d, q ≤ a ∨ b ≤ q)
    (ht : a < t ∧ t < b) (x : ℝ) (hx : (a:ℝ) < x ∧ x < (b:ℝ)) :
    (∀ i, (x*(d i:ℝ) ≤ 1-(P:ℝ) ↔ t*d i ≤ 1-P)) ∧
    (∀ i, (1 ≤ x*(d i:ℝ) ↔ 1 ≤ t*d i)) := by
  have ht' : (a:ℝ) < (t:ℝ) ∧ (t:ℝ) < (b:ℝ) := by exact_mod_cast ht
  have hh := same_interval_cuts (breakpoints P d) a b hgap x t hx ht'
  have hcuts : ∀ i, (x*(d i:ℝ) ≤ 1-(P:ℝ) ↔ t*d i ≤ 1-P) ∧
      (1 ≤ x*(d i:ℝ) ↔ 1 ≤ t*d i) := by
    intro i
    by_cases hz : d i=0
    · simp only [hz,Rat.cast_zero,mul_zero]
      constructor
      · have hp : (0:ℝ) ≤ 1-(P:ℝ) := by exact_mod_cast (sub_nonneg.mpr hP.le)
        exact iff_of_true hp (sub_nonneg.mpr hP.le)
      · norm_num
    · have hdi : 0 < d i := lt_of_le_of_ne (hd i) (Ne.symm hz)
      have hdR : (0:ℝ) < d i := by exact_mod_cast hdi
      have hcut1 : (1-P)/d i ∈ breakpoints P d := by
        exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_univ i))))
      have hcut2 : 1/d i ∈ breakpoints P d := by
        exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (mem_univ i))))
      have h1 := (hh _ hcut1).1
      have h2 := (hh _ hcut2).2
      simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_one] at h1 h2
      rw [le_div_iff₀ hdR,le_div_iff₀ hdR] at h1
      rw [div_le_iff₀ hdR,div_le_iff₀ hdR] at h2
      constructor
      · exact h1.trans (by norm_cast)
      · exact h2.trans (by norm_cast)
  exact ⟨fun i => (hcuts i).1,fun i => (hcuts i).2⟩

end MetricKMedian.Taper
end
end

end OAI
