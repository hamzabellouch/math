import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Candidates.ConstituentMultiplicity
import OAI.Combinatorics.BalancedRyser.Probability.LogTail
import OAI.Combinatorics.BalancedRyser.Probability.ProbabilityPerturbation

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offsetLaw_eq_uniform : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
  unfold offsetLaw
  congr 1
  exact Subsingleton.elim _ _

theorem sampledMultiplicity_tail (p : Point F) (m : ℕ) :
    offsetEventProbability {M : MergedPairs F | m ≤ sampledMultiplicity M p} ≤
      (((2 * (Fintype.card F + 1)).choose m : ℕ) : ℝ) /
        (Fintype.card F : ℝ) ^ m := by
  classical
  let e := Equiv.curry (Direction F) Bool F
  have he := uniform_toOuterMeasure_equiv e
    {M : MergedPairs F | m ≤ sampledMultiplicity M p}
  have h := uniform_many_coordinate_matches_le
    (fun ds : Direction F × Bool => lineEval ds.1 p) m
  unfold offsetEventProbability
  rw [offsetLaw_eq_uniform, ← he]
  simpa [e, Equiv.curry, Function.curry, sampledMultiplicity, OnLine, constituent,
    eq_comm, Fintype.card_prod, Fintype.card_option, Nat.mul_comm] using h

theorem sampledMultiplicity_some_point_tail (m : ℕ) :
    offsetEventProbability {M : MergedPairs F | ∃ p, m ≤ sampledMultiplicity M p} ≤
      (Fintype.card F : ℝ) ^ 2 *
        ((((2 * (Fintype.card F + 1)).choose m : ℕ) : ℝ) /
          (Fintype.card F : ℝ) ^ m) := by
  classical
  let e := Equiv.curry (Direction F) Bool F
  have he := uniform_toOuterMeasure_equiv e
    {M : MergedPairs F | ∃ p, m ≤ sampledMultiplicity M p}
  have h := uniform_exists_many_coordinate_matches_le
    (fun (p : Point F) (ds : Direction F × Bool) => lineEval ds.1 p) m
  unfold offsetEventProbability
  rw [offsetLaw_eq_uniform, ← he]
  simpa [e, Equiv.curry, Function.curry, sampledMultiplicity, OnLine, constituent,
    Point, eq_comm, Fintype.card_prod, Fintype.card_option, Nat.mul_comm,
    Nat.cast_mul, pow_two] using h

open Filter Topology

theorem tendsto_sampledMultiplicity_bad
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) < sampledMultiplicity M p})
      atTop (𝓝 0) := by
  have hbound := (BalancedRyser.tendsto_polynomial_mul_slot_choose_tail 2 1
    (by norm_num)).comp hq
  have hbound' : Tendsto (fun n => (Fintype.card (F n) : ℝ) ^ 2 *
      (((2 * (Fintype.card (F n) + 1)).choose
        (Nat.ceil (Real.log (Fintype.card (F n) : ℝ))) : ℝ) /
      (Fintype.card (F n) : ℝ) ^ Nat.ceil (Real.log (Fintype.card (F n) : ℝ))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, mul_assoc] using hbound
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ hbound'
  intro n
  calc
    _ ≤ offsetEventProbability (F := F n)
        {M | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) ≤ sampledMultiplicity M p} := by
      apply pmf_outerReal_mono (offsetLaw (F n))
      intro M hM
      obtain ⟨p, hp⟩ := hM
      exact ⟨p, hp.le⟩
    _ ≤ _ := sampledMultiplicity_some_point_tail _

theorem tendsto_sampledMultiplicity_good
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card (F n) : ℝ))})
      atTop (𝓝 1) := by
  have heq (n : ℕ) : offsetEventProbability (F := F n)
      {M | ∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card (F n) : ℝ))} =
      1 - offsetEventProbability (F := F n)
        {M | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) < sampledMultiplicity M p} := by
    have hset : {M : MergedPairs (F n) | ∀ p, sampledMultiplicity M p ≤
        Nat.ceil (Real.log (Fintype.card (F n) : ℝ))} =
        {M : MergedPairs (F n) | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) <
          sampledMultiplicity M p}ᶜ := by
      ext M
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
    rw [hset, offsetEventProbability, pmf_outerReal_compl]
    rfl
  simpa only [heq, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_sampledMultiplicity_bad F hq)

theorem tendsto_polynomial_sampledMultiplicity_tail
    (r : ℕ) (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => (Fintype.card (F n) : ℝ) ^ r *
      offsetEventProbability (F := F n)
        {M | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) ≤ sampledMultiplicity M p})
      atTop (𝓝 0) := by
  have hbound := (BalancedRyser.tendsto_polynomial_mul_slot_choose_tail (r + 2) 1
    (by norm_num)).comp hq
  have hbound' : Tendsto (fun n => (Fintype.card (F n) : ℝ) ^ r *
      ((Fintype.card (F n) : ℝ) ^ 2 *
        ((((2 * (Fintype.card (F n) + 1)).choose
          (Nat.ceil (Real.log (Fintype.card (F n) : ℝ)))) : ℝ) /
          (Fintype.card (F n) : ℝ) ^ Nat.ceil (Real.log (Fintype.card (F n) : ℝ)))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_add, div_pow, one_pow, div_eq_mul_inv,
      one_mul, inv_pow, mul_assoc] using hbound
  apply squeeze_zero (fun n => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    ENNReal.toReal_nonneg) _ hbound'
  intro n
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  exact sampledMultiplicity_some_point_tail _

end Balanced

end OAI
