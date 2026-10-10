import OAI.NumberTheory.JointDickman.Amplification.FiniteGraphFluctuation
import OAI.NumberTheory.JointDickman.Counting.ArithmeticBlockMatrix

namespace OAI

/-! # The finite graph kernel is the original block matrix before normalization -/

namespace JointDickman
open Finset Classical

theorem rawArithmeticGraphKernel_outside {B L T N n : ℕ} {τ C : ℝ} {j : ℤ}
    (hn : n ∉ Icc 1 (arithmeticGraphVertexCap B N)) :
    rawArithmeticGraphKernel B L τ C T N j n = 0 := by
  unfold rawArithmeticGraphKernel
  apply sum_eq_zero
  intro g hg
  have hh : ¬ (graphTripleLag g = j ∧ n ∈ graphTripleEdges N g) :=
    fun h => hn (graphTriple_edges_subset hg h.2)
  exact ite_eq_right hh

theorem arithmeticBlockMatrix_eq_finiteGraph (B L T H M N u : ℕ) (τ C : ℝ) (i k : Fin M) :
    arithmeticBlockMatrix B L τ C T N H M (u : ℤ) i k =
      finiteGraphKernel B L T H M N u τ C i k/((T : ℝ)*N) := by
  have hj : ((k.val : ℤ)+1)-((i.val : ℤ)+1) = (k.val : ℤ)-i.val := by ring
  have hn : (u : ℤ)+((i.val : ℤ)+1) = ((u+(i.val+1) : ℕ) : ℤ) := by push_cast; ring
  unfold arithmeticBlockMatrix finiteGraphKernel
  dsimp only
  rw [hj,hn,Int.toNat_natCast]
  let j : ℤ := (k.val : ℤ)-i.val
  let n := u+(i.val+1)
  change (if j ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
      (n : ℤ) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ)
    then rawArithmeticGraphKernel B L τ C T N j n/((B : ℝ)*T*N) else 0) =
      (if H < j.natAbs then rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) else 0)/((T : ℝ)*N)
  by_cases hlag : j ∈ nonzeroShortLags T \ nonzeroShortLags H
  · have hspec : (j ≠ 0 ∧ j.natAbs ≤ T) ∧ ¬ (j ≠ 0 ∧ j.natAbs ≤ H) := by
      simpa only [mem_sdiff,mem_nonzeroShortLags] using hlag
    have hH : H < j.natAbs := by omega
    by_cases hv : (n : ℤ) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ)
    · rw [ite_eq_left ⟨hlag,hv⟩,ite_eq_left hH,div_div]
      congr 1
      ring
    · have hvn : n ∉ Icc 1 (arithmeticGraphVertexCap B N) := by
        intro h
        apply hv
        exact mem_Icc.mpr ⟨by exact_mod_cast (mem_Icc.mp h).1,by exact_mod_cast (mem_Icc.mp h).2⟩
      rw [ite_eq_right (fun h => hv h.2),ite_eq_left hH,rawArithmeticGraphKernel_outside hvn]
      simp only [zero_div]
  · have hcond : ¬ (j ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
        (n : ℤ) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ)) := fun h => hlag h.1
    rw [ite_eq_right hcond]
    by_cases hH : H < j.natAbs
    · have hj0 : j ≠ 0 := by intro hz; simp [hz] at hH
      have hlarge : T ≤ j.natAbs := by
        by_contra hh
        apply hlag
        exact mem_sdiff.mpr ⟨mem_nonzeroShortLags.mpr ⟨hj0,by omega⟩,
          fun h => (Nat.not_le_of_lt hH) (mem_nonzeroShortLags.mp h).2⟩
      rw [ite_eq_left hH,rawArithmeticGraphKernel_large_lag B L τ C T N j n hlarge]
      simp only [zero_div]
    · simp only [hH,ite_false,zero_div]

end JointDickman

end OAI
