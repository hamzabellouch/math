import Mathlib
import OAI.Geometry.PrescribedRicci.DiscreteInterpolation

namespace OAI

/-! Discrete Many Product. -/

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace TameInterpolation

lemma positive_sequence_log_bound (m : ℕ) (hm : 0 < m)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (C : ℝ) (hC : 0 < C)
    (hr : ∀ i, i+2 ≤ m → (a (i+1))^2 ≤ C*a i*a (i+2))
    (j : ℕ) (hj : j ≤ m) :
    Real.log (a j) ≤ ((j:ℝ)/(m:ℝ))*Real.log (a m) +
      (1-(j:ℝ)/(m:ℝ))*Real.log (a 0) + ((j:ℝ)*((m:ℝ)-(j:ℝ))/2)*Real.log C := by
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  let z : ℕ → ℝ := fun i => Real.log (a i) - ((i:ℝ)/(m:ℝ))*Real.log (a m) -
    (1-(i:ℝ)/(m:ℝ))*Real.log (a 0) - ((i:ℝ)*((m:ℝ)-(i:ℝ))/2)*Real.log C
  have hz0 : z 0 ≤ 0 := by simp [z]
  have hzm : z m ≤ 0 := by simp [z,hm']
  have hzr (i : ℕ) (hi : i+2 ≤ m) : 2*z (i+1) ≤ z i+z (i+2) := by
    have hlog := Real.log_le_log (sq_pos_of_pos (ha (i+1))) (hr i hi)
    rw [Real.log_pow,Real.log_mul (mul_ne_zero hC.ne' (ha i).ne') (ha (i+2)).ne',
      Real.log_mul hC.ne' (ha i).ne'] at hlog
    have he : z i+z (i+2)-2*z (i+1) =
        Real.log (a i)+Real.log (a (i+2))-2*Real.log (a (i+1))+Real.log C := by
      dsimp [z]
      push_cast
      ring
    norm_num only [Nat.cast_ofNat] at hlog
    linarith only [hlog,he]
  have h := discrete_maximum m z hz0 hzm hzr j hj
  dsimp [z] at h
  linarith only [h]

lemma positive_sequence_many (m : ℕ) (hm : 0 < m)
    (a : ℕ → ℝ) (ha : ∀ i, 0 < a i) (C : ℝ) (hC : 1 ≤ C)
    (hr : ∀ i, i+2 ≤ m → (a (i+1))^2 ≤ C*a i*a (i+2))
    {ι : Type*} (s : Finset ι) (j : ι → ℕ) (hs : ∑ i ∈ s, j i = m) :
    ∏ i ∈ s, a (j i) ≤ C^(∑ i ∈ s, j i*(m-j i))*a 0^(s.card-1)*a m := by
  have hC0 : 0 < C := by linarith only [hC]
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hsn : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at hs
    omega
  have hj (i : ι) (hi : i ∈ s) : j i ≤ m := by
    rw [← hs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hc : (s.card:ℝ)-1 = ((s.card-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by simpa using hsn.card_pos),Nat.cast_one]
  have hs' : ∑ i ∈ s, (j i:ℝ)/(m:ℝ) = 1 := by
    rw [← Finset.sum_div,← Nat.cast_sum,hs,div_self hm']
  have he1 : ∑ i ∈ s, (j i:ℝ)/(m:ℝ)*Real.log (a m) = Real.log (a m) := by
    rw [← Finset.sum_mul,hs',one_mul]
  have he2 : ∑ i ∈ s, (1-(j i:ℝ)/(m:ℝ))*Real.log (a 0) = ((s.card-1:ℕ):ℝ)*Real.log (a 0) := by
    rw [← Finset.sum_mul,Finset.sum_sub_distrib,hs']
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hc]
  have he3 : ∑ i ∈ s, ((j i:ℝ)*((m:ℝ)-(j i:ℝ))/2)*Real.log C ≤
      ((∑ i ∈ s, j i*(m-j i):ℕ):ℝ)*Real.log C := by
    rw [Nat.cast_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [Nat.cast_mul,Nat.cast_sub (hj i hi)]
    have hnon : 0 ≤ (j i:ℝ)*((m:ℝ)-(j i:ℝ)) := by
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hj i hi))
    have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
    nlinarith only [hnon,hlogC,mul_nonneg hnon hlogC]
  have hlog : ∑ i ∈ s, Real.log (a (j i)) ≤
      ((∑ i ∈ s, j i*(m-j i):ℕ):ℝ)*Real.log C + ((s.card-1:ℕ):ℝ)*Real.log (a 0)+Real.log (a m) := by
    have hh := Finset.sum_le_sum (fun i hi => positive_sequence_log_bound m hm a ha C hC0 hr (j i) (hj i hi))
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,he1,he2] at hh
    linarith only [hh,he3]
  have hl : Real.log (∏ i ∈ s, a (j i)) = ∑ i ∈ s, Real.log (a (j i)) :=
    Real.log_prod (fun _ _ => (ha _).ne')
  have hp : 0 < ∏ i ∈ s, a (j i) := Finset.prod_pos (fun _ _ => ha _)
  have hrp : 0 < C^(∑ i ∈ s, j i*(m-j i))*a 0^(s.card-1)*a m := mul_pos (mul_pos (pow_pos hC0 _) (pow_pos (ha 0) _)) (ha m)
  have hrlog : Real.log (C^(∑ i ∈ s, j i*(m-j i))*a 0^(s.card-1)*a m) =
      ((∑ i ∈ s, j i*(m-j i):ℕ):ℝ)*Real.log C + ((s.card-1:ℕ):ℝ)*Real.log (a 0)+Real.log (a m) := by
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hC0.ne') (pow_ne_zero _ (ha 0).ne')) (ha m).ne',
      Real.log_mul (pow_ne_zero _ hC0.ne') (pow_ne_zero _ (ha 0).ne'),Real.log_pow,Real.log_pow]
  rw [← hl,← hrlog] at hlog
  exact (Real.log_le_log_iff hp hrp).mp hlog

lemma nonnegative_sequence_many (m : ℕ) (hm : 0 < m)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (C : ℝ) (hC : 1 ≤ C)
    (hr : ∀ i, i+2 ≤ m → (a (i+1))^2 ≤ C*a i*a (i+2))
    {ι : Type*} (s : Finset ι) (j : ι → ℕ) (hs : ∑ i ∈ s, j i = m) :
    ∏ i ∈ s, a (j i) ≤ C^(∑ i ∈ s, j i*(m-j i))*a 0^(s.card-1)*a m := by
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ∏ i ∈ s, a (j i) ≤ C^(∑ i ∈ s, j i*(m-j i))*(max (a 0) ε)^(s.card-1)*max (a m) ε := by
    apply (Finset.prod_le_prod₀ (fun i _ => ha (j i)) (fun i _ => le_max_left (a (j i)) ε)).trans
    exact positive_sequence_many m hm (fun i => max (a i) ε)
      (fun i => hε.trans_le (le_max_right _ _)) C hC (clamp_recurrence m a ha C hC hr ε hε) s j hs
  have hcont : Continuous (fun ε : ℝ => C^(∑ i ∈ s, j i*(m-j i))*(max (a 0) ε)^(s.card-1)*max (a m) ε) := by
    fun_prop
  have hlim : Tendsto (fun ε : ℝ => C^(∑ i ∈ s, j i*(m-j i))*(max (a 0) ε)^(s.card-1)*max (a m) ε)
      (𝓝[>] 0) (𝓝 (C^(∑ i ∈ s, j i*(m-j i))*a 0^(s.card-1)*a m)) := by
    simpa only [max_eq_left (ha 0),max_eq_left (ha m)] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε
end TameInterpolation

end

end OAI
