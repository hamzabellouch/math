import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridTrace.NatGrid

lemma dyadic_pointwise (v : Vertex → ℝ) {N M : ℕ} {x : Vertex}
    (hx : x ∈ square N) (hM : N < 2^M)
    (hscale : ∀ k < M, 2^k ≤ N) :
    |v x-avg (square N) v| ≤
      ∑ k ∈ Finset.range M, (4/((2:ℝ)^k)) *
        ∑ e ∈ edges (lo x (2*(2^k)-1)) (hi N x (2*(2^k)-1)), edgeGrad v e := by
  let a (k : ℕ) := avg (box N x (2^k-1)) v
  have h0 : a 0 = v x := by simp [a,box_zero hx,avg]
  have hlast : a M = avg (square N) v := by
    change avg (box N x (2^M-1)) v = _
    rw [box_full hx (by omega)]
  have h := dist_le_range_sum_dist a M
  rw [Real.dist_eq,h0,hlast] at h
  refine h.trans (Finset.sum_le_sum (fun k hk => ?_))
  have hstep := dyadic_step v hx (2^k) (Nat.one_le_two_pow) (hscale k (Finset.mem_range.mp hk))
  simpa [a,Real.dist_eq,pow_succ,mul_comm,Nat.cast_pow] using hstep

lemma weighted_telescope {N M : ℕ} (ν v : Vertex → ℝ)
    (hν : ∀ x ∈ square N, 0 ≤ ν x) (hM : N < 2^M)
    (hscale : ∀ k < M, 2^k ≤ N) :
    |(∑ x ∈ square N, ν x*v x)-(∑ x ∈ square N, ν x)*avg (square N) v| ≤
      ∑ k ∈ Finset.range M, ∑ e ∈ edges (0,0) (N,N), localKernel N ν (2^k) e*edgeGrad v e := by
  have heq : (∑ x ∈ square N, ν x*v x)-(∑ x ∈ square N, ν x)*avg (square N) v =
      ∑ x ∈ square N, ν x*(v x-avg (square N) v) := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [heq]
  calc
    _ ≤ ∑ x ∈ square N, |ν x*(v x-avg (square N) v)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ square N, ν x*|v x-avg (square N) v| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul,abs_of_nonneg (hν x hx)]
    _ ≤ ∑ x ∈ square N, ν x*(∑ k ∈ Finset.range M, (4/((2:ℝ)^k))*
        ∑ e ∈ edges (lo x (2*(2^k)-1)) (hi N x (2*(2^k)-1)), edgeGrad v e) :=
      Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (dyadic_pointwise v hx hM hscale) (hν x hx))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [localKernel,Nat.cast_pow]
      simp only [mul_assoc,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      have hs := box_edges_subset N x (2*(2^k)-1)
      calc
        _ = ∑ e ∈ edges (0,0) (N,N),
            if e ∈ edges (lo x (2*(2^k)-1)) (hi N x (2*(2^k)-1)) then
              ν x*((4/(2:ℝ)^k)*edgeGrad v e) else 0 := by
          rw [← Finset.sum_filter]
          congr 1
          ext e
          simp only [Finset.mem_filter]
          exact ⟨fun h => ⟨hs h,h⟩,fun h => h.2⟩
        _ = _ := by
          apply Finset.sum_congr rfl
          intro e he
          split_ifs <;> ring

end GridTrace.NatGrid

end

end OAI
