import OAI.NumberTheory.JointDickman.Probability.CyclicKernelPartialSums

namespace OAI

/-! # The rational geometric-kernel sum, including its zero-frequency peak -/
namespace JointDickman
open Finset

lemma sum_positive_multiples (L q : ℕ) :
    (∑ n ∈ Icc 1 L, if q ∣ n then (1:ℝ) else 0) = ((L/q:ℕ):ℝ) := by
  have hi : Icc 1 L = Ico 1 (L+1) := by
    ext n
    simp only [mem_Icc,mem_Ico]
    omega
  have hs : (∑ n ∈ Icc 1 L, if q ∣ n then (1:ℝ) else 0) =
      ∑ n ∈ range L, if q ∣ n+1 then (1:ℝ) else 0 := by
    rw [hi]
    symm
    simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using
      sum_Ico_add' (fun n => if q ∣ n then (1:ℝ) else 0) 0 L 1
  rw [hs,sum_boole,Nat.card_multiples]

theorem cyclic_kernel_sum_bound {q : ℕ} [NeZero q] (N L : ℕ) (u : (ZMod q)ˣ) :
    (∑ n ∈ Icc 1 L, cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) ≤
      (N:ℝ)^2*(L:ℝ)/q + (N:ℝ)*((L:ℝ)+2*q) := by
  have hzero (n : ℕ) (hn : q ∣ n) :
      cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) = (N:ℝ)^2 := by
    have hz := (ZMod.natCast_eq_zero_iff n q).mpr hn
    rw [hz,zero_mul,cyclicGeometricKernel_zero]
  have hsplit (n : ℕ) : cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) =
      (if q ∣ n then (N:ℝ)^2 else 0) +
      (if q ∣ n then 0 else cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) := by
    by_cases hn : q ∣ n <;> simp [hn,hzero]
  have hpeak : (∑ n ∈ Icc 1 L, if q ∣ n then (N:ℝ)^2 else 0) =
      (N:ℝ)^2*((L/q:ℕ):ℝ) := by
    calc
      _ = (N:ℝ)^2*(∑ n ∈ Icc 1 L, if q ∣ n then (1:ℝ) else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        split_ifs <;> simp
      _ = _ := by rw [sum_positive_multiples]
  have hsum : (∑ n ∈ Icc 1 L, cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) =
      (N:ℝ)^2*((L/q:ℕ):ℝ) +
      ∑ n ∈ Icc 1 L, if q ∣ n then 0 else cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) := by
    have ht := sum_congr rfl (fun n (_ : n ∈ Icc 1 L) => hsplit n)
    rw [ht,sum_add_distrib,hpeak]
  have hdiv : ((L/q:ℕ):ℝ) ≤ (L:ℝ)/q := by
    apply (le_div_iff₀ (by exact_mod_cast NeZero.pos q : (0:ℝ) < q)).mpr
    exact_mod_cast Nat.div_mul_le_self L q
  rw [hsum]
  exact add_le_add (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hdiv (sq_nonneg (N:ℝ)))
    (cyclic_kernel_nonzero_partial_bound N L u)

end JointDickman

end OAI
