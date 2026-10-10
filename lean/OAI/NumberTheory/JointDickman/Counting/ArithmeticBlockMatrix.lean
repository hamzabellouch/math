import OAI.NumberTheory.JointDickman.Counting.BlockMatrixIndices
import OAI.NumberTheory.JointDickman.Counting.SamplingTransfer

namespace OAI

/-! # The actual block energy as a quadratic form of a finite matrix -/

namespace JointDickman
open Finset

noncomputable def arithmeticBlockMatrix (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (s : ℤ) (i k : Fin M) : ℝ :=
  let j := ((k.val : ℤ)+1)-((i.val : ℤ)+1)
  let n := s+((i.val : ℤ)+1)
  if j ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
      n ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
    rawArithmeticGraphKernel B L τ C T N j n.toNat/((B : ℝ)*T*N)
  else 0

noncomputable def blockLabels (M : ℕ) (s : ℤ) (F : ℕ → ℂ) (i : Fin M) : ℂ :=
  F (s+((i.val : ℤ)+1)).toNat

theorem complexEnergy_re_pair {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).re = ∑ i, ∑ k, K i k*(star (z i)*z k).re := by
  simp [complexEnergy, mul_assoc]

theorem arithmeticBlockMatrix_energy (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (s : ℤ) (F : ℕ → ℂ) :
    (complexEnergy (arithmeticBlockMatrix B L τ C T N H M s) (blockLabels M s F)).re =
      ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
        if k-i ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+i ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F (k-i) (s+i) else 0 := by
  rw [complexEnergy_re_pair]
  have hp (i k : Fin M) :
      arithmeticBlockMatrix B L τ C T N H M s i k *
          (star (blockLabels M s F i)*blockLabels M s F k).re =
        if ((k.val : ℤ)+1)-((i.val : ℤ)+1) ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+((i.val : ℤ)+1) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F
            (((k.val : ℤ)+1)-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)) else 0 := by
    unfold arithmeticBlockMatrix blockLabels
    dsimp only
    split_ifs with h
    · have hn : 0 ≤ s+((i.val : ℤ)+1) := le_trans (by norm_num) (mem_Icc.mp h.2).1
      have he : ((s+((i.val : ℤ)+1)).toNat : ℤ)+
          (((k.val : ℤ)+1)-((i.val : ℤ)+1)) = s+((k.val : ℤ)+1) := by
        rw [Int.toNat_of_nonneg hn]
        ring
      unfold arithmeticVertexCorrelation
      rw [he]
      ring
    · simp
  simp_rw [hp]
  calc
    _ = ∑ i : Fin M, ∑ k ∈ Icc 1 (M : ℤ),
        if k-((i.val : ℤ)+1) ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+((i.val : ℤ)+1) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F
            (k-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)) else 0 := by
      apply sum_congr rfl
      intro i _
      exact sum_block_indices M (fun k : ℤ =>
        if k-((i.val : ℤ)+1) ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+((i.val : ℤ)+1) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F
            (k-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)) else 0)
    _ = _ := sum_block_indices M (fun i : ℤ => ∑ k ∈ Icc 1 (M : ℤ),
      if k-i ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
          s+i ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
        arithmeticVertexCorrelation B L τ C T N F (k-i) (s+i) else 0)

theorem arithmeticBlockAverage_matrix (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) :
    arithmeticBlockAverage B L τ C T N H M F =
      (∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        (complexEnergy (arithmeticBlockMatrix B L τ C T N H M s)
          (blockLabels M s F)).re)/(M : ℝ) := by
  rw [arithmeticBlockAverage_square]
  simp_rw [arithmeticBlockMatrix_energy]

end JointDickman

end OAI
