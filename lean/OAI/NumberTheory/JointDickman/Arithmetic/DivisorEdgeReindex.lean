import OAI.NumberTheory.JointDickman.Arithmetic.DivisorEdgeEndpoints

namespace OAI

/-! # Exact finite transport from multiplier sums to additive graph endpoints -/

namespace JointDickman
open Finset

noncomputable def divisorEdgeInverse (a b c n : ℕ) : ℕ := (c*(n/b)-1)/a

noncomputable def divisorEdgeOld (a b c N : ℕ) : Finset ℕ :=
  (range N).filter (fun m => a*m < N ∧ b*m < N ∧ c ∣ a*m+1 ∧ c ∣ b*m+1)

noncomputable def divisorEdgeNew (a b c N : ℕ) (j : ℤ) : Finset ℕ :=
  (Icc 1 (b*N)).filter (fun n => b ∣ n ∧ (a : ℤ) ∣ (n : ℤ)+j ∧
    a*divisorEdgeInverse a b c n < N ∧ b*divisorEdgeInverse a b c n < N)

theorem divisorEdgeInverse_eq {a b c n m : ℕ} (ha : 0 < a)
    (h : c*(n/b) = a*m+1) : divisorEdgeInverse a b c n = m := by
  unfold divisorEdgeInverse
  rw [h,Nat.add_sub_cancel,Nat.mul_div_cancel_left m ha]

/-- Membership in the multiplier sum gives an endpoint with exactly the
inverse multiplier; the finite endpoints include every original summand. -/
theorem divisorEdge_forward_mem {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) {m : ℕ} (hm : m ∈ divisorEdgeOld a b c N) :
    b*((a*m+1)/c) ∈ divisorEdgeNew a b c N j ∧
      divisorEdgeInverse a b c (b*((a*m+1)/c)) = m := by
  classical
  obtain ⟨_,ham,hbm,hca,hcb⟩ := mem_filter.mp hm
  let z := (a*m+1)/c
  have hcz : c*z = a*m+1 := Nat.mul_div_cancel' hca
  have hz : 0 < z := by nlinarith
  have hdiv : b ∣ b*z := dvd_mul_right b z
  have hnb : (b*z)/b = z := Nat.mul_div_cancel_left z hb
  have hinv : divisorEdgeInverse a b c (b*z) = m :=
    divisorEdgeInverse_eq ha (by rw [hnb]; exact hcz)
  refine ⟨?_,hinv⟩
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hb hz,?_⟩,hdiv,?_,?_,?_⟩
  · have hzN : z ≤ N := (Nat.div_le_self _ _).trans (by omega)
    exact Nat.mul_le_mul_left b hzN
  · have hends := natural_divisor_edge_endpoints hc hca hcb he
    rw [hends]
    exact_mod_cast (dvd_mul_right a ((b*m+1)/c))
  · change a*divisorEdgeInverse a b c (b*z) < N
    rwa [hinv]
  · change b*divisorEdgeInverse a b c (b*z) < N
    rwa [hinv]

/-- Every allowed endpoint reconstructs one old multiplier. -/
theorem divisorEdge_inverse_mem {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (he : (a : ℤ)-b = j*c)
    (hcop : a.Coprime j.natAbs) {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    divisorEdgeInverse a b c n ∈ divisorEdgeOld a b c N ∧
      b*((a*divisorEdgeInverse a b c n+1)/c) = n := by
  classical
  obtain ⟨hnrange,hbn,hd,ham,hbm⟩ := mem_filter.mp hn
  have hn0 : 0 < n := (mem_Icc.mp hnrange).1
  obtain ⟨m,hm,_⟩ := natural_divisor_edge_inverse ha hc hn0 hbn he hcop hd
  have hinv : divisorEdgeInverse a b c n = m := divisorEdgeInverse_eq ha hm
  have hca : c ∣ a*m+1 := by rw [← hm]; exact dvd_mul_right c (n/b)
  have hcb : c ∣ b*m+1 := by
    have hdiff : (c : ℤ) ∣ (a : ℤ)-b := ⟨j,by simpa only [mul_comm] using he⟩
    have hx : (c : ℤ) ∣ (a : ℤ)*m+1 := by exact_mod_cast hca
    have hy := dvd_sub hx (dvd_mul_of_dvd_left hdiff (m : ℤ))
    have hz : (a : ℤ)*m+1-((a : ℤ)-b)*m = (b : ℤ)*m+1 := by ring
    rw [hz] at hy
    exact_mod_cast hy
  have hmN : m < N := by
    rw [hinv] at ham
    exact (Nat.le_mul_of_pos_left m ha).trans_lt ham
  rw [hinv]
  refine ⟨mem_filter.mpr ⟨mem_range.mpr hmN,?_,?_,?_,?_⟩,?_⟩
  · simpa only [hinv] using ham
  · simpa only [hinv] using hbm
  · simpa only [hinv] using hca
  · simpa only [hinv] using hcb
  · rw [← hm,Nat.mul_div_cancel_left _ hc]
    exact Nat.mul_div_cancel' hbn

/-- A bijective finite-sum reindexing, with no error term or multiplicity. -/
theorem sum_divisorEdge_reindex {M : Type*} [AddCommMonoid M]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {j : ℤ} (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (N : ℕ) (F : ℕ → M) :
    (∑ m ∈ divisorEdgeOld a b c N, F m) =
      ∑ n ∈ divisorEdgeNew a b c N j, F (divisorEdgeInverse a b c n) := by
  classical
  apply sum_bij (fun m _ => b*((a*m+1)/c))
  · intro m hm
    exact (divisorEdge_forward_mem ha hb hc he hm).1
  · intro m hm k hk heq
    have hm' := (divisorEdge_forward_mem ha hb hc he hm).2
    have hk' := (divisorEdge_forward_mem ha hb hc he hk).2
    rw [← hm',← hk',heq]
  · intro n hn
    have h := divisorEdge_inverse_mem ha hc he hcop hn
    exact ⟨_,h.1,h.2⟩
  · intro m hm
    rw [(divisorEdge_forward_mem ha hb hc he hm).2]

end JointDickman

end OAI
