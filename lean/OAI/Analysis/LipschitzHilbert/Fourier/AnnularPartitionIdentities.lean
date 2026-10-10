import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPositiveCutoff

namespace OAI

/-! The positive and negative annular cutoffs reconstruct the actual
low-pass difference, whose finite geometric sums telescope exactly. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem reassemblyPositive_halfsum_nonneg (s : ℝ) (hs : 0≤s) :
    reassemblyPositive s+reassemblyPositive (-s)=reassemblyDifference s := by
  have hminus : reassemblyOuter (-s)=0 := by
    by_contra hn
    have h := (reassemblyOuter_support (-s) hn).1
    linarith only [h,hs]
  rw [reassemblyPositive_apply,reassemblyPositive_apply,hminus,zero_mul,add_zero]
  by_cases hd : reassemblyDifference s=0
  · simp only [hd,mul_zero]
  · have hlo : 9/8 < |s| := lt_of_not_ge (fun h => hd (reassemblyDifference_small s h))
    have hhi : |s|<117/64 := lt_of_not_ge (fun h => hd (reassemblyDifference_large s h))
    rw [abs_of_nonneg hs] at hlo hhi
    rw [reassemblyOuter_one s ⟨hlo.le,by linarith only [hhi]⟩,one_mul]

theorem reassemblyPositive_halfsum (s : ℝ) :
    reassemblyPositive s+reassemblyPositive (-s)=reassemblyDifference s := by
  by_cases hs : 0≤s
  · exact reassemblyPositive_halfsum_nonneg s hs
  · simpa only [neg_neg,reassemblyDifference_even,add_comm] using
      reassemblyPositive_halfsum_nonneg (-s) (neg_nonneg.mpr (le_of_not_ge hs))

theorem reassemblyPositive_reflected_sum (s : ℝ) :
    reassemblyPositive s+conjugateReflectedCutoff reassemblyPositive s=reassemblyDifference s := by
  rw [conjugateReflectedCutoff_apply]
  change reassemblyPositive s+star (reassemblyPositive (-s))=_
  rw [reassemblyPositive_real,reassemblyPositive_halfsum]

theorem reassemblyDifference_step (n : ℕ) (s : ℝ) :
    reassemblyDifference ((3/2:ℝ)^n*s)=
      reassemblyLow ((16/27)*((3/2:ℝ)^n*s))-
        reassemblyLow ((16/27)*((3/2:ℝ)^(n+1)*s)) := by
  unfold reassemblyDifference
  congr 2
  rw [pow_succ]
  ring

theorem reassemblyDifference_telescope (N : ℕ) (s : ℝ) :
    (∑ n∈Finset.range N, reassemblyDifference ((3/2:ℝ)^n*s))=
      reassemblyLow ((16/27)*s)-reassemblyLow ((16/27)*((3/2:ℝ)^N*s)) := by
  induction N with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,pow_zero,one_mul,sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,reassemblyDifference_step]
    ring

theorem reassembly_signed_telescope (N : ℕ) (s : ℝ) :
    (∑ n∈Finset.range N, (reassemblyPositive ((3/2:ℝ)^n*s)+
      conjugateReflectedCutoff reassemblyPositive ((3/2:ℝ)^n*s)))=
      reassemblyLow ((16/27)*s)-reassemblyLow ((16/27)*((3/2:ℝ)^N*s)) := by
  simp only [reassemblyPositive_reflected_sum]
  exact reassemblyDifference_telescope N s

end LipschitzHilbert.PacketRepresentation

end

end OAI
