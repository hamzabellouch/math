import OAI.Combinatorics.ContingencyTables.Sampling.ExactInputBounds
import OAI.Combinatorics.ContingencyTables.Machines.ScheduledCountInput

namespace OAI

/-! # Charging scalar tabulation loops to the ordinary sampler's word -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma parameterDimension_pos (z : SamplingParameters) : 0 < parameterDimension z := by
  unfold parameterDimension marginDimension
  omega

lemma parameterBinaryLength_pos (z : SamplingParameters) : 0 < parameterBinaryLength z := by
  have h := parameterDimension_pos z
  unfold parameterBinaryLength marginBinaryLength parameterDimension at *
  omega

lemma parameterSteps_pos (z : SamplingParameters) : 0 < parameterSteps z := by
  unfold parameterSteps
  exact Nat.mul_pos (pow_pos (parameterDimension_pos z) _)
    (pow_pos (by have := parameterBinaryLength_pos z; omega) _)

lemma parameterTrials_pos (z : SamplingParameters) : 0 < parameterTrials z := by
  unfold parameterTrials
  exact Nat.mul_pos (pow_pos (parameterDimension_pos z) _) (by omega)

lemma parameterCompletionWidth_pos (z : SamplingParameters) : 0 < parameterCompletionWidth z := by
  unfold parameterCompletionWidth
  exact Nat.mul_pos (by decide) (pow_pos (by omega) _)

lemma parameterDimension_le_steps (z : SamplingParameters) :
    parameterDimension z ≤ parameterSteps z := by
  have hd : 1 ≤ parameterDimension z := parameterDimension_pos z
  have hb : 1 ≤ z.2+parameterBinaryLength z := by have := parameterBinaryLength_pos z; omega
  exact (Nat.le_self_pow (by decide : 200 ≠ 0) _).trans (by
    unfold parameterSteps
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((parameterDimension z)^200)
      (one_le_pow₀ hb : 1 ≤ (z.2+parameterBinaryLength z)^2))

lemma parameterBinaryLength_le_steps (z : SamplingParameters) :
    parameterBinaryLength z ≤ parameterSteps z := by
  have hd : 1 ≤ (parameterDimension z)^200 := one_le_pow₀ (parameterDimension_pos z)
  have hb : parameterBinaryLength z ≤ (z.2+parameterBinaryLength z)^2 :=
    (Nat.le_add_left _ _).trans (Nat.le_self_pow (by decide) _)
  unfold parameterSteps
  exact hb.trans (by simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right ((z.2+parameterBinaryLength z)^2) hd)

lemma parameterAccuracy_le_steps (z : SamplingParameters) :
    parameterAccuracy z ≤ parameterSteps z := by
  unfold parameterAccuracy parameterSteps
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (parameterDimension_pos z) (by decide))

theorem schedule_numeric_polynomial : ∃ p : Polynomial ℕ,∀ z,
    parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤
      p.eval (scheduledCountInputMeasure z) := by
  refine ⟨2*X+25*(3*X+1)^62,?_⟩
  intro z
  let M := scheduledCountInputMeasure z
  have hs : parameterSteps z ≤ M := by unfold M scheduledCountInputMeasure; omega
  have hd := (parameterDimension_le_steps z).trans hs
  have hb := (parameterBinaryLength_le_steps z).trans hs
  have ha := (parameterAccuracy_le_steps z).trans hs
  have hf : parameterCompletionWidth z ≤ 25*(3*M+1)^62 := by
    unfold parameterCompletionWidth
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  simp only [eval_add,eval_mul,eval_pow,eval_ofNat,eval_X,eval_one]
  change _ ≤ 2*M+25*(3*M+1)^62
  omega

lemma scheduledCountInputMeasure_le (z : SamplingParameters) :
    scheduledCountInputMeasure z ≤ 4*parameterWordCount z+weight z := by
  let N := parameterSteps z
  let J := parameterTrials z
  let P := parameterProposalWidth z
  let F := parameterCompletionWidth z
  let A := N*(P+F)+F
  have hN : 1 ≤ N := parameterSteps_pos z
  have hJ : 1 ≤ J := parameterTrials_pos z
  have hF : 1 ≤ F := parameterCompletionWidth_pos z
  have hNF : N ≤ N*(P+F) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (show 1 ≤ P+F by omega)
  have hPF : P+F ≤ N*(P+F) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (P+F) hN
  have hA : 1 ≤ A := by unfold A; omega
  have hAW : A ≤ J*A := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right A hJ
  have hJW : J ≤ J*A := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left J hA
  have hT : scheduledTrialWidth z ≤ A := by
    unfold scheduledTrialWidth scheduledDenseWidth scheduledUnitWidth
    change (if hasLargeRectangle z then N*(P+F)+F else N*P) ≤ A
    split_ifs
    · exact le_rfl
    · unfold A
      exact (Nat.mul_le_mul_left N (Nat.le_add_right P F)).trans (Nat.le_add_right _ _)
  change N+J+P+scheduledTrialWidth z+weight z ≤ 4*(J*A)+weight z
  have hNA : N ≤ A := by unfold A; omega
  have hPA : P ≤ A := by unfold A; omega
  have hnw := hNA.trans hAW
  have hpw := hPA.trans hAW
  have htw := hT.trans hAW
  omega

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms Polynomial
open scoped BigOperators Classical
noncomputable section

theorem exact_count_input_measure_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j →
      scheduledCountInputMeasure (exactSamplingParameters (List.ofFn r,List.ofFn c)) ≤
        p.eval (Algorithms.samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := exact_ordinary_bits_polynomial
  obtain ⟨q,hq⟩ := exact_margin_weight_polynomial
  obtain ⟨u,hu⟩ := polynomial_exactSamplingParameters
  refine ⟨4*p+u.comp q,?_⟩
  intro m n r c htotal
  have hw : weight (exactSamplingParameters (List.ofFn r,List.ofFn c)) ≤
      u.eval (q.eval (Algorithms.samplingSize n r 0)) :=
    (Nat.le_add_left _ _).trans ((hu (List.ofFn r,List.ofFn c)).trans
    (polynomial_eval_monotone u (hq m n r c htotal)))
  have hb : parameterWordCount (exactSamplingParameters (List.ofFn r,List.ofFn c)) ≤
      p.eval (Algorithms.samplingSize n r 0) := hp m n r c
  have hs := scheduledCountInputMeasure_le (exactSamplingParameters (List.ofFn r,List.ofFn c))
  simp only [eval_add,eval_mul,eval_ofNat,eval_comp]
  omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
