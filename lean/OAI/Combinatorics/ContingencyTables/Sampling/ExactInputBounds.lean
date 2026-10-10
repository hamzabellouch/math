import OAI.Combinatorics.ContingencyTables.Sampling.ExactGateCost
import OAI.Combinatorics.ContingencyTables.Sampling.ExactPrintCost
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperInputWordBudget

namespace OAI

/-! # Exact-sampler parameters in the public binary input size -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec
open ProfilePrograms DensePrograms Algorithms Polynomial
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "S" => samplingSize n r 0

lemma exact_public_length (htotal : (∑ i,r i)=∑ j,c j) :
    (encodeMargins r c).length ≤ 5*S^2 := by
  have h := encodeSamplingInput_length r c htotal 0
  have he : (encodeMargins r c).length ≤ (encodeSamplingInput r c 0).length := by
    simp only [encodeSamplingInput,List.length_append]
    omega
  exact he.trans h

lemma exact_public_weight (htotal : (∑ i,r i)=∑ j,c j) :
    weight (encodeMargins r c) ≤ 91*S^2 := by
  have h := exact_public_length r c htotal
  have hS : 1 ≤ S^2 := one_le_pow₀ (by unfold samplingSize; omega)
  rw [weight_word]
  omega

lemma exact_precision_bound : correctionPrecision r c ≤ 245^8*S^16 := by
  let dim := CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)
  have hi := sampling_internal_size_bound r c 0
  have hd : dim ≤ 245*S^2 := by dsimp only [dim]; omega
  have hb : smallBinaryLength r c ≤ 245*S^2 := by omega
  change dim^6*(smallBinaryLength r c)^2 ≤ _
  calc
    _ ≤ (245*S^2)^6*(245*S^2)^2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left hb _)
    _ = 245^8*S^16 := by ring

lemma exact_margin_weight_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → weight (List.ofFn r,List.ofFn c) ≤ p.eval (samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := polynomial_exactParsedMargins
  refine ⟨p.comp (91*X^2),?_⟩
  intro m n r c htotal
  have h := (Nat.le_add_left _ _).trans (hp (encodeMargins r c))
  rw [exactParsedMargins_spec] at h
  exact h.trans (by
    rw [eval_comp]
    simp only [eval_mul,eval_ofNat,eval_pow,eval_X]
    exact polynomial_eval_monotone p (exact_public_weight r c htotal))

lemma exact_parameter_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → exactParameterMeasure (List.ofFn r,List.ofFn c) ≤
        p.eval (samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := exact_margin_weight_polynomial
  refine ⟨C (245^8)*X^16+p,?_⟩
  intro m n r c htotal
  simp only [exactParameterMeasure,exactPrecision_ofFn,eval_add,eval_mul,eval_C,eval_pow,eval_X]
  exact Nat.add_le_add (exact_precision_bound r c) (hp m n r c htotal)

lemma exact_total_weight : weight (∑ i,r i) ≤ 4*S+1 := by
  have hs : (∑ i,r i).size ≤ Nat.clog 2 ((∑ i,r i)+1) :=
    Nat.size_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_pow_clog (by decide) _))
  have hw := weight_nat_le (∑ i,r i)
  unfold samplingSize
  omega

lemma exact_matrix_size : ExactPrintCost.matrixSize (n := n) r ≤ 25*S^3 := by
  have hS : 1 ≤ S := by unfold samplingSize; omega
  have hm : m ≤ S := by unfold samplingSize; omega
  have hn : n ≤ S := by unfold samplingSize; omega
  have hw : 4*weight (∑ i,r i)+2 ≤ 22*S := by
    have := exact_total_weight (n := n) r
    omega
  have hpow : S ≤ S^3 := Nat.le_self_pow (by decide) _
  calc
    _ ≤ S*(S*(22*S)+2)+1 := by unfold ExactPrintCost.matrixSize; gcongr
    _ ≤ 25*S^3 := by nlinarith

lemma exact_ordinary_bits_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      exactOrdinaryBits (List.ofFn r,List.ofFn c) ≤ p.eval (samplingSize n r 0) := by
  let q : Polynomial ℕ := X+2*(C (245^8)*X^16)
  refine ⟨C (344^644)*q^1288,?_⟩
  intro m n r c
  have hD := exact_precision_bound r c
  have hS : samplingSize n r (2*correctionPrecision r c) ≤ q.eval (samplingSize n r 0) := by
    simp only [q,eval_add,eval_mul,eval_ofNat,eval_C,eval_pow,eval_X]
    unfold samplingSize at *
    omega
  rw [exactOrdinaryBits_ofFn]
  have hf : finiteSamplerBits r c (2*correctionPrecision r c) ≤
      344^644*(samplingSize n r (2*correctionPrecision r c))^1288 :=
    sampling_word_budget_polynomial r c (2*correctionPrecision r c)
  have hp (k : ℕ) :
      344^644*(samplingSize n r (2*correctionPrecision r c))^k ≤
        (C (344^644)*q^k).eval (samplingSize n r 0) := by
    rw [eval_mul,eval_C,eval_pow]
    exact Nat.mul_le_mul_left (344^644) (Nat.pow_le_pow_left hS k)
  exact hf.trans (hp 1288)

lemma exact_gate_measure_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → ExactGateCost.measure (List.ofFn r,List.ofFn c) ≤
        p.eval (samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := exact_parameter_polynomial
  obtain ⟨q,hq⟩ := exact_margin_weight_polynomial
  obtain ⟨u,hu⟩ := exact_ordinary_bits_polynomial
  refine ⟨p+q+u,?_⟩
  intro m n r c htotal
  simpa only [ExactGateCost.measure,FiniteWordExecution.wordMeasure,eval_add,add_assoc]
    using Nat.add_le_add (hp m n r c htotal)
      (Nat.add_le_add (hq m n r c htotal) (hu m n r c))

end
end ContingencyTables.SmallGraphProfiles

end OAI
