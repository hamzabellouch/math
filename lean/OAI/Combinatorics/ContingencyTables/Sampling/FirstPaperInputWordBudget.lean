import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperWordBudget
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBinaryParameters
import OAI.Combinatorics.ContingencyTables.AlgorithmStatements

namespace OAI

/-! # The sampler's bit budget in the original binary input parameters -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators
open CompletionCounts Algorithms

private lemma scaled_square_pow (a x n : ℕ) : (a*x^2)^n=a^n*x^(2*n) := by
  rw [mul_pow,←pow_mul]

private lemma scaled_square_pow644 (a x : ℕ) : (a*x^2)^644=a^644*x^1288 := by
  have h := scaled_square_pow a x 644
  have he : a^644*x^(2*644)=a^644*x^1288 :=
    congrArg (fun t => a^644*x^t) (by decide)
  exact h.trans he

private lemma power_mono_left (a b e : ℕ) (h : a ≤ b) : a^e ≤ b^e :=
  Nat.pow_le_pow_left h e

private lemma word_budget_scaled (d b k a S : ℕ) (hsize : d+b+k+100 ≤ a*S^2) :
    smallSamplerWordBudget d b k ≤ a^644*S^1288 := by
  calc
    _ ≤ (d+b+k+100)^644 := smallSamplerWordBudget_polynomial d b k
    _ ≤ (a*S^2)^644 := power_mono_left (d+b+k+100) (a*S^2) 644 hsize
    _ = a^644*S^1288 := scaled_square_pow644 a S

lemma sampling_dimension_bound (m n l k : ℕ) :
    dimensionAllowance (I := Fin m) (J := Fin n) ≤ 11*(m+n+l+k+1)^2 := by
  let S := m+n+l+k+1
  have hm : m+1 ≤ S := by omega
  have hn : n+1 ≤ S := by omega
  have hp : (m+1)*(n+1) ≤ S^2 := by simpa only [pow_two] using Nat.mul_le_mul hm hn
  have hS : 1 ≤ S^2 := one_le_pow₀ (by omega : 1 ≤ S)
  simp only [dimensionAllowance,Fintype.card_fin]
  change 10+(m+1)*(n+1) ≤ 11*S^2
  omega

lemma sampling_internal_size_bound {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) :
    dimensionAllowance (I := Fin m) (J := Fin n)+smallBinaryLength r c+k+1 ≤
      245*(samplingSize n r k)^2 := by
  let l := Nat.clog 2 ((∑ i,r i)+1)
  let S := samplingSize n r k
  have hb := smallBinaryLength_le r c
  have hd := sampling_dimension_bound m n l k
  change dimensionAllowance (I := Fin m) (J := Fin n) ≤ 11*S^2 at hd
  have hS : S ≤ S^2 := Nat.le_self_pow (by decide) S
  have hk : l+k+3 ≤ 3*S := by dsimp [S,samplingSize,l]; omega
  change dimensionAllowance (I := Fin m) (J := Fin n)+smallBinaryLength r c+k+1 ≤ 245*S^2
  omega

/-- All fixed random-bit segments together have a uniform polynomial
bound in dimensions, binary total margin, and requested accuracy. -/
theorem sampling_word_budget_polynomial {m n : ℕ}
    (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) :
    smallSamplerWordBudget (dimensionAllowance (I := Fin m) (J := Fin n))
      (smallBinaryLength r c) k ≤
      344^644*(samplingSize n r k)^1288 := by
  have hs : 1 ≤ (samplingSize n r k)^2 := one_le_pow₀ (by unfold samplingSize; omega)
  have hi := sampling_internal_size_bound r c k
  have hb : dimensionAllowance (I := Fin m) (J := Fin n)+smallBinaryLength r c+k+100 ≤
      344*(samplingSize n r k)^2 := by omega
  exact word_budget_scaled (dimensionAllowance (I := Fin m) (J := Fin n))
    (smallBinaryLength r c) k 344 (samplingSize n r k) hb

end ContingencyTables.SmallGraphProfiles

end OAI
