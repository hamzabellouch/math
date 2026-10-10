import OAI.NumberTheory.JointDickman.Counting.CyclicGeometricEnergy
import OAI.NumberTheory.JointDickman.Counting.PeriodicPositiveSums

namespace OAI

/-! # Partial sums of nonzero rational frequencies -/
namespace JointDickman
open Finset

lemma cyclicGeometricKernel_zero {q : ℕ} [NeZero q] (N : ℕ) :
    cyclicGeometricKernel N (0:ZMod q) = (N:ℝ)^2 := by
  simp [cyclicGeometricKernel]

/-- The nonzero frequencies in any initial segment contribute only O(N(L+q)). -/
theorem cyclic_kernel_nonzero_partial_bound {q : ℕ} [NeZero q]
    (N L : ℕ) (u : (ZMod q)ˣ) :
    (∑ n ∈ Icc 1 L, if q ∣ n then 0 else
      cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q))) ≤
      (N:ℝ)*((L:ℝ)+2*q) := by
  classical
  let g : ZMod q → ℝ := fun x => if x=0 then 0 else cyclicGeometricKernel N x
  let f : ZMod q → ℝ := fun x => g (u.mulRight x)
  have hg (x : ZMod q) : 0 ≤ g x := by
    dsimp [g]
    split_ifs
    · exact le_rfl
    · exact cyclicGeometricKernel_nonneg _ _
  have hperiodg : (∑ x : ZMod q, g x) ≤ (q:ℝ)*N := by
    calc
      _ ≤ ∑ x : ZMod q, cyclicGeometricKernel (N%q) x := by
        apply sum_le_sum
        intro x hx
        by_cases hx0 : x=0
        · simpa only [g,ite_eq_left hx0] using cyclicGeometricKernel_nonneg (N%q) x
        · simp only [g,ite_eq_right hx0,cyclicGeometricKernel_mod N x hx0]
          exact le_rfl
      _ = (q:ℝ)*((N%q:ℕ):ℝ) := cyclicGeometricKernel_complete (Nat.mod_lt N (NeZero.pos q)).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N q) (Nat.cast_nonneg q)
  have hperiod : (∑ x : ZMod q, f x) ≤ (q:ℝ)*N := by
    have he : (∑ x : ZMod q, f x) = ∑ x : ZMod q, g x :=
      Fintype.sum_equiv u.mulRight _ _ (fun _ => rfl)
    rw [he]
    exact hperiodg
  have hvalue (n : ℕ) : f (n:ZMod q) = if q ∣ n then 0 else
      cyclicGeometricKernel N ((n:ZMod q)*(u:ZMod q)) := by
    have hz : ((n:ZMod q)*(u:ZMod q)=0) ↔ (n:ZMod q)=0 := by
      constructor
      · intro hn
        apply u.mulRight.injective
        simpa only [Units.mulRight_apply,zero_mul] using hn
      · intro hn
        simp [hn]
    change (if (n:ZMod q)*(u:ZMod q)=0 then 0 else _) = _
    simp only [hz,ZMod.natCast_eq_zero_iff,Units.mulRight_apply]
  have hpre := periodic_nonnegative_prefix_bound f (fun x => hg _) (Nat.cast_nonneg N)
    hperiod (L+1)
  have hsub : Icc 1 L ⊆ range (L+1) := by
    intro n hn
    simp only [mem_Icc,mem_range] at hn ⊢
    omega
  have hsum : (∑ n ∈ Icc 1 L, f (n:ZMod q)) ≤
      ∑ n ∈ range (L+1), f (n:ZMod q) :=
    sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hg _)
  simp_rw [←hvalue]
  refine hsum.trans (hpre.trans ?_)
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  push_cast
  nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

end JointDickman

end OAI
