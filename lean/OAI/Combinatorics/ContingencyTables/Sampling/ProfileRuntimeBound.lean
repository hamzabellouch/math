import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicMachine
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperInputWordBudget
import OAI.Combinatorics.ContingencyTables.Machines.PublicInputLength

namespace OAI

/-! # A uniform public polynomial bound for the physical sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec Polynomial
open scoped BigOperators

lemma polynomial_scaled_power (p : Polynomial ℕ) (A x b : ℕ) (hx : 1≤x) :
    p.eval (A*x^b)≤p.eval A*x^(b*p.natDegree) := by
  rw [p.eval_eq_sum_range,p.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i≤p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [mul_pow,←pow_mul]
  calc
    p.coeff i*(A^i*x^(b*i))=(p.coeff i*A^i)*x^(b*i) := by ring
    _ ≤ (p.coeff i*A^i)*x^(b*p.natDegree) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (Nat.mul_le_mul_left b hi'))
    _ = _ := by ring

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec
open Algorithms Polynomial
open scoped BigOperators Classical

noncomputable section

private lemma wordMeasure_from_bounds (L W S A : ℕ)
    (hL : L≤5*S^2) (hW : W≤A*S^1288) (hS : 1≤S) :
    18*L+1+W≤(A+91)*S^1288 := by
  have hexp : (2:ℕ)≤1288 := by decide
  have hpow : S^2≤S^1288 := pow_le_pow_right₀ hS hexp
  have hone : 1≤S^1288 := one_le_pow₀ hS
  calc
    18*L+1+W ≤ 18*(5*S^2)+S^1288+A*S^1288 :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hL) hone) hW
    _ ≤ 18*(5*S^1288)+S^1288+A*S^1288 := by gcongr
    _ = (A+91)*S^1288 := by
      rw [Nat.add_mul]
      omega

lemma public_wordMeasure_bound {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) :
    FiniteWordExecution.wordMeasure publicWordCount (encodeSamplingInput r c k)≤
      (344^644+91)*(samplingSize n r k)^1288 := by
  have hl := encodeSamplingInput_length r c htotal k
  have hw := sampling_word_budget_polynomial r c k
  have hS : 1 ≤ samplingSize n r k := by unfold samplingSize; omega
  unfold FiniteWordExecution.wordMeasure
  rw [weight_word,publicWordCount_spec]
  change 18*(encodeSamplingInput r c k).length+1+finiteSamplerBits r c k≤_
  exact wordMeasure_from_bounds _ _ _ _ hl hw hS

/-- The explicit binary word count and physical compiler yield one
polynomial bound in the manuscript's public input parameters. -/
theorem samplingMachineTime_public_bound :
    ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → ∀ k,
      samplingMachineTime (encodeSamplingInput r c k)≤C*(samplingSize n r k)^d := by
  obtain ⟨p,hp⟩ := samplingMachineTime_polynomial
  refine ⟨p.eval (344^644+91)+1,1288*p.natDegree,by omega,?_⟩
  intro m n r c htotal k
  have hS : 1 ≤ samplingSize n r k := by unfold samplingSize; omega
  calc
    _ ≤ p.eval (FiniteWordExecution.wordMeasure publicWordCount (encodeSamplingInput r c k)) := hp _
    _ ≤ p.eval ((344^644+91)*(samplingSize n r k)^1288) :=
      polynomial_eval_monotone p (public_wordMeasure_bound r c htotal k)
    _ ≤ p.eval (344^644+91)*(samplingSize n r k)^(1288*p.natDegree) :=
      polynomial_scaled_power p (344^644+91) (samplingSize n r k) 1288 hS
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

end
end ContingencyTables.SmallGraphProfiles

end OAI
