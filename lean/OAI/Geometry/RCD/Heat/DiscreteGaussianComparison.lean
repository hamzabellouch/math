import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace OAI

/-! # A finite comparison principle for the Gaussian midpoint recurrence -/

noncomputable section
namespace RegularPointCoordinates

theorem discrete_strict_maximum_principle {v : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (h0 : v 0 ≤ 0) (hn : v n ≤ 0)
    (hm : ∀ j, 0 < j → j < n → v j ≤ a*(v (j-1)+v (j+1))/2) :
    ∀ j, j ≤ n → v j ≤ 0 := by
  intro i hi
  by_contra hbad
  have hpos : 0 < v i := lt_of_not_ge hbad
  obtain ⟨j,hj,hmax⟩ := (Finset.range (n+1)).exists_max_image v ⟨0,by simp⟩
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hvj : 0 < v j := hpos.trans_le (hmax i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi)))
  have hj0 : 0 < j := by
    by_contra hz
    have he : j=0 := by omega
    subst j
    linarith
  have hjlt : j < n := by
    by_contra hz
    have he : j=n := by omega
    subst j
    linarith
  have hl : v (j-1) ≤ v j := hmax (j-1) (Finset.mem_range.mpr (by omega))
  have hr : v (j+1) ≤ v j := hmax (j+1) (Finset.mem_range.mpr (by omega))
  have havg : (v (j-1)+v (j+1))/2 ≤ v j := by linarith
  have hscale := mul_le_mul_of_nonneg_left havg ha0
  have hsmall := mul_lt_of_lt_one_left hvj ha1
  have hrec := hm j hj0 hjlt
  nlinarith

theorem discrete_gaussian_comparison {u h : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (h0 : h 0 ≤ u 0) (hn : h n ≤ u n)
    (hu : ∀ j, 0 < j → j < n → a*(u (j-1)+u (j+1))/2 ≤ u j)
    (hh : ∀ j, 0 < j → j < n → h j ≤ a*(h (j-1)+h (j+1))/2) :
    ∀ j, j ≤ n → h j ≤ u j := by
  have hm : ∀ j, 0 < j → j < n →
      (h j-u j) ≤ a*((h (j-1)-u (j-1))+(h (j+1)-u (j+1)))/2 := by
    intro j hj0 hjn
    have hx := hu j hj0 hjn
    have hy := hh j hj0 hjn
    nlinarith only [hx,hy]
  have hc := discrete_strict_maximum_principle ha0 ha1 (sub_nonpos.mpr h0) (sub_nonpos.mpr hn) hm
  intro j hj
  exact sub_nonpos.mp (hc j hj)

end RegularPointCoordinates

end

end OAI
