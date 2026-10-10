import OAI.NumberTheory.JointDickman.Counting.BlockEndpointLoss
import OAI.NumberTheory.JointDickman.Counting.BlockReindex

namespace OAI

/-! # Exact finite block expression for the arithmetic graph energy -/

namespace JointDickman
open Finset

theorem sum_int_Icc_toNat (V : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 (V : ℤ), f n.toNat) = ∑ n ∈ Icc 1 V, f n := by
  apply sum_bij (fun n _ => n.toNat)
  · intro n hn
    have h := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n hn m hm he
    have hn' := mem_Icc.mp hn
    have hm' := mem_Icc.mp hm
    omega
  · intro n hn
    refine ⟨(n : ℤ),?_,by simp⟩
    have h := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n _
    rfl

noncomputable def arithmeticVertexCorrelation (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) (j n : ℤ) : ℝ :=
  (rawArithmeticGraphKernel B L τ C T N j n.toNat *
    (star (F n.toNat)*F ((n.toNat : ℤ)+j).toNat).re)/((B : ℝ)*T*N)

theorem sum_arithmeticVertexCorrelation (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) (j : ℤ) :
    (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ),
      arithmeticVertexCorrelation B L τ C T N F j n) =
        kernelLagCorrelation B L τ C T N j F := by
  unfold arithmeticVertexCorrelation
  rw [sum_int_Icc_toNat (arithmeticGraphVertexCap B N) (fun n : ℕ =>
    (rawArithmeticGraphKernel B L τ C T N j n *
      (star (F n)*F ((n : ℤ)+j).toNat).re)/((B : ℝ)*T*N)), ← sum_div]
  rfl

noncomputable def arithmeticBlockAverage (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) : ℝ :=
  finiteBlockAverage M (arithmeticGraphVertexCap B N)
    (nonzeroShortLags T \ nonzeroShortLags H)
    (arithmeticVertexCorrelation B L τ C T N F)

theorem arithmeticBlockAverage_eq_weighted (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (hM : 0 < M) (hTM : T ≤ M) (F : ℕ → ℂ) :
    arithmeticBlockAverage B L τ C T N H M F =
      blockWeightedGraphEnergy B L τ C T N H M F := by
  unfold arithmeticBlockAverage blockWeightedGraphEnergy
  rw [finiteBlockAverage_eq M _ hM]
  · simp_rw [sum_arithmeticVertexCorrelation]
  · intro j hj
    exact ((mem_nonzeroShortLags.mp (mem_sdiff.mp hj).1).2).trans hTM

theorem arithmeticBlockAverage_square (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) :
    arithmeticBlockAverage B L τ C T N H M F =
      (∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
          if k-i ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
              s+i ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
            arithmeticVertexCorrelation B L τ C T N F (k-i) (s+i) else 0)/(M : ℝ) := by
  exact finiteBlockAverage_square ..

end JointDickman

end OAI
