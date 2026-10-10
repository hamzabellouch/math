import Mathlib

namespace OAI

                                       
section

/-! Height-free parked coefficient finance. A logarithmic tail telescope gives
 the manuscript's dyadic-group estimate directly, using the same shared subtree
 capacity; no independence or average-state premise is used. -/
noncomputable section
namespace UniformKServer.ParkCoefficients
open Finset
open scoped Classical

def tail (b : ℕ→ℝ) (N j : ℕ) : ℝ := ∑ i∈Ico j N, b i

theorem tail_nonneg (b : ℕ→ℝ) (hb : ∀ i, 0≤b i) (N j : ℕ) : 0≤tail b N j :=
  sum_nonneg fun i _ => hb i

theorem tail_step (b : ℕ→ℝ) (N j : ℕ) (hj : j<N) : tail b N j=b j+tail b N (j+1) := by
  simp only [tail,sum_Ico_eq_sub _ (Nat.le_of_lt hj),sum_Ico_eq_sub _ (by omega : j+1≤N),sum_range_succ]
  ring

theorem tail_end (b : ℕ→ℝ) (N : ℕ) : tail b N N=0 := by simp [tail]

theorem log_increment (c u v : ℝ) (hc : 0<c) (hu : 0≤u) (hv : 0≤v) :
    u/(c+u+v)≤Real.log (c+u+v)-Real.log (c+v) := by
  have h1 : 0<c+v := by linarith
  have h2 : 0<c+u+v := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos h2 h1)
  rw [Real.log_div h2.ne' h1.ne'] at h
  have he : 1-((c+u+v)/(c+v))⁻¹=u/(c+u+v) := by field_simp; ring
  rwa [he] at h

theorem reciprocal_telescope (c : ℝ) (hc : 0<c) (b : ℕ→ℝ) (hb : ∀ i, 0≤b i) (N : ℕ) :
    (∑ j∈range N, b j/(c+tail b N j))≤Real.log (c+tail b N 0)-Real.log c := by
  have h (j : ℕ) (hj : j∈range N) : b j/(c+tail b N j)≤
      Real.log (c+tail b N j)-Real.log (c+tail b N (j+1)) := by
    rw [tail_step b N j (mem_range.mp hj),←add_assoc]
    exact log_increment c (b j) (tail b N (j+1)) hc (hb j) (tail_nonneg b hb N _)
  have hs := sum_le_sum h
  rw [sum_range_sub',tail_end,add_zero] at hs
  exact hs

theorem capacity_telescope (c K : ℝ) (hc : 0<c) (hK : 1≤K)
    (b A : ℕ→ℝ) (hb : ∀ i, 0≤b i) (N : ℕ)
    (hA : ∀ j, 1≤A j) (hcap : ∀ j<N, tail b N j≤c*(A j-1))
    (htotal : tail b N 0≤c*(K-1)) :
    (∑ j∈range N, b j/A j)≤c*Real.log K := by
  have hp (j : ℕ) (hj : j<N) : b j/A j≤c*(b j/(c+tail b N j)) := by
    have ht := tail_nonneg b hb N j
    have hd : 0<c+tail b N j := by linarith
    have ha : 0<A j := by linarith [hA j]
    have hca : c+tail b N j≤c*A j := by linarith [hcap j hj]
    apply (div_le_iff₀ ha).mpr
    have he : c*(b j/(c+tail b N j))*A j=(c*b j*A j)/(c+tail b N j) := by ring
    rw [he]
    exact (le_div_iff₀ hd).mpr (by nlinarith [mul_le_mul_of_nonneg_left hca (hb j)])
  have hs := sum_le_sum fun j hj => hp j (mem_range.mp hj)
  rw [←mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left (reciprocal_telescope c hc b hb N) hc.le
  have hlog : Real.log (c+tail b N 0)-Real.log c≤Real.log K := by
    rw [←Real.log_div (by linarith [tail_nonneg b hb N 0]) hc.ne']
    apply (Real.log_le_log_iff
      (div_pos (by linarith [tail_nonneg b hb N 0]) hc)
      (lt_of_lt_of_le zero_lt_one hK)).mpr
    apply (div_le_iff₀ hc).mpr
    nlinarith
  exact (hs.trans ht).trans (mul_le_mul_of_nonneg_left hlog hc.le)

end UniformKServer.ParkCoefficients

end


end

end OAI
