import OAI.NumberTheory.JointDickman.Amplification.MonotoneSumComparison
import OAI.NumberTheory.JointDickman.Amplification.GcdReciprocalMean
import Mathlib.NumberTheory.Chebyshev

namespace OAI

/-! # The logarithmically weighted reciprocal-prime sum -/
namespace JointDickman
open Finset

lemma sum_primesLE_shifted {R : Type*} [AddCommMonoid R] (F : ℕ → R) (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, F p) = ∑ i ∈ range N, if (i+1).Prime then F (i+1) else 0 := by
  have hs : Nat.primesLE N = (Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,mem_filter,mem_Icc]
    constructor
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨hp.one_le,hpN⟩,hp⟩
    · rintro ⟨⟨hp1,hpN⟩,hp⟩
      exact ⟨hpN,hp⟩
  rw [hs,sum_filter]
  have hi : Icc 1 N = Ico 1 (N+1) := by
    ext i
    simp only [mem_Icc,mem_Ico]
    omega
  rw [hi]
  symm
  simpa only [Nat.zero_add,Nat.Ico_zero_eq_range] using
    sum_Ico_add' (fun n => if n.Prime then F n else 0) 0 N 1

theorem prime_log_reciprocal_sum_le (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, Real.log p/(p:ℝ)) ≤ Real.log 4*(1+Real.log N) := by
  let f := fun i : ℕ => if (i+1).Prime then Real.log ((i+1:ℕ):ℝ) else 0
  let w := fun i : ℕ => 1/((i+1:ℕ):ℝ)
  have hprefix (k : ℕ) (hk : k ≤ N) :
      (∑ i ∈ range k, f i) ≤ ∑ _i ∈ range k, Real.log 4 := by
    have he : (∑ i ∈ range k, f i) = Chebyshev.theta k := by
      rw [Chebyshev.theta_eq_sum_primesLE_log]
      exact (sum_primesLE_shifted (fun n => Real.log n) k).symm
    rw [he]
    simpa [mul_comm] using Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg k)
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; positivity
  have hanti : Antitone w := by
    intro i j hij
    dsimp [w]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hcompare := antitone_weighted_sum_le f (fun _ => Real.log 4) w N hw hanti hprefix
  have hleft : (∑ p ∈ Nat.primesLE N, Real.log p/(p:ℝ)) = ∑ i ∈ range N, w i*f i := by
    rw [sum_primesLE_shifted]
    apply sum_congr rfl
    intro i hi
    dsimp [w,f]
    split_ifs <;> ring
  have hrecip : (∑ i ∈ range N, w i) ≤ 1+Real.log N := by
    have he : (∑ i ∈ range N, w i) = ∑ r ∈ Ioc 0 N, 1/(r:ℝ) := by
      have hi : Ioc 0 N = Ico 1 (N+1) := by
        ext r
        simp only [mem_Ioc,mem_Ico]
        omega
      rw [hi]
      simpa only [w,Nat.zero_add,Nat.Ico_zero_eq_range] using
        sum_Ico_add' (fun n : ℕ => 1/(n:ℝ)) 0 N 1
    rw [he]
    exact reciprocal_initial_sum N
  rw [hleft]
  apply hcompare.trans
  have hr : (∑ i ∈ range N, w i*Real.log 4) = Real.log 4*∑ i ∈ range N, w i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hr]
  exact mul_le_mul_of_nonneg_left hrecip (Real.log_nonneg (by norm_num))

end JointDickman

end OAI
