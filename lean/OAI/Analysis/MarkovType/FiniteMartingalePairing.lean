import OAI.Analysis.MarkovType.FiniteConditionalMartingale
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteLaw

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem expect_pair_key_right_clm (μ : FiniteLaw Ω) (key : Ω → K)
    (G : Ω → E →L[ℝ] ℝ) (H : K → E) :
    μ.expect (fun ω => G ω (H (key ω))) = ∑ a, (μ.fiberSum key G a) (H a) := by
  symm
  simp only [fiberSum, sum_apply,
    smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_mul]

theorem expect_pair_key_left_clm (μ : FiniteLaw Ω) (key : Ω → K)
    (H : K → E →L[ℝ] ℝ) (f : Ω → E) :
    μ.expect (fun ω => H (key ω) (f ω)) = ∑ a, H a (μ.fiberSum key f a) := by
  symm
  simp only [fiberSum, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_mul]

theorem expect_pair_conditionalAverage_clm (μ : FiniteLaw Ω) (key : Ω → K)
    (f : Ω → E) (G : Ω → E →L[ℝ] ℝ) :
    μ.expect (fun ω => G ω (μ.conditionalAverage key f ω)) =
      μ.expect (fun ω => (μ.conditionalAverage key G ω) (f ω)) := by
  change μ.expect (fun ω => G ω (μ.conditionalMean key f (key ω))) =
    μ.expect (fun ω => (μ.conditionalMean key G (key ω)) (f ω))
  rw [μ.expect_pair_key_right_clm, μ.expect_pair_key_left_clm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [conditionalMean, map_smul, smul_apply]

end FiniteLaw

namespace FinitePartitionFiltration

theorem expect_pair_conditionalProcess_of_adapted (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) {G : Ω → E →L[ℝ] ℝ}
    (hG : F.AdaptedAt j G) :
    μ.expect (fun ω => G ω (F.conditionalProcess μ f j ω)) =
      μ.expect (fun ω => G ω (f ω)) := by
  classical
  rw [conditionalProcess, μ.expect_pair_conditionalAverage_clm]
  let key : Ω → Quotient (F.part j) := Quotient.mk (F.part j)
  let H : Quotient (F.part j) → E →L[ℝ] ℝ :=
    Quotient.lift G (fun _ _ h => hG h)
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  have h := μ.mass_smul_conditionalAverage_key key H ω
  change μ.mass ω • μ.conditionalAverage (Quotient.mk (F.part j)) G ω =
    μ.mass ω • G ω at h
  have he := congrArg (fun L : E →L[ℝ] ℝ => L (f ω)) h
  simpa only [smul_apply, smul_eq_mul] using he

end FinitePartitionFiltration

theorem HasZeroConditionalSum.expect_pair_of_atom_constant
    {μ : FiniteLaw Ω} {P : Setoid Ω} {G : Ω → E →L[ℝ] ℝ}
    (hG : HasZeroConditionalSum μ P G) (z : Ω → E)
    (hz : ∀ {ω η}, P.r ω η → z ω = z η) :
    μ.expect (fun ω => G ω (z ω)) = 0 := by
  classical
  let key : Ω → Quotient P := Quotient.mk P
  let H : Quotient P → E := Quotient.lift z (fun _ _ h => hz h)
  change μ.expect (fun ω => G ω (H (key ω))) = 0
  rw [μ.expect_pair_key_right_clm]
  apply Finset.sum_eq_zero
  intro a _
  have hsum : μ.fiberSum key G a = 0 := by
    refine Quotient.inductionOn a ?_
    intro ω
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, key,
      Quotient.eq, ite_smul, zero_smul] using hG ω
  simp only [hsum, zero_apply]

theorem sum_finiteDifference_eq (M : ℕ → Ω → E) (N : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range (N + 1), finiteDifference M j ω) = M N ω := by
  induction N with
  | zero =>
      change (∑ j ∈ Finset.range 1, finiteDifference M j ω) = M 0 ω
      exact (Finset.sum_range_one _).trans (congrFun (finiteDifference_zero M) ω)
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, finiteDifference_succ]
      abel

theorem finite_martingale_difference_pairing
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {G : ℕ → Ω → E →L[ℝ] ℝ} {N j : ℕ}
    (hG : F.IsMartingaleUpTo μ G N) (f : Ω → E) (hj : j ≤ N) :
    μ.expect (fun ω => finiteDifference G j ω (f ω)) =
      μ.expect (fun ω => finiteDifference G j ω
        (finiteDifference (F.conditionalProcess μ f) j ω)) := by
  have ha := F.expect_pair_conditionalProcess_of_adapted μ f j
    (hG.difference_adapted hj)
  cases j with
  | zero =>
      simpa only [finiteDifference_zero] using ha.symm
  | succ k =>
      have hz : HasZeroConditionalSum μ (F.part k) (finiteDifference G (k + 1)) := by
        simpa only [Nat.add_sub_cancel] using hG.2 (k + 1) (Nat.succ_pos k) hj
      have hzero := hz.expect_pair_of_atom_constant
        (F.conditionalProcess μ f k) (F.adaptedAt_conditionalProcess μ f k)
      have hsub :
          μ.expect (fun ω => finiteDifference G (k + 1) ω
            (F.conditionalProcess μ f (k + 1) ω - F.conditionalProcess μ f k ω)) =
          μ.expect (fun ω => finiteDifference G (k + 1) ω
            (F.conditionalProcess μ f (k + 1) ω)) -
          μ.expect (fun ω => finiteDifference G (k + 1) ω
            (F.conditionalProcess μ f k ω)) := by
        simp only [map_sub, FiniteLaw.expect, mul_sub, Finset.sum_sub_distrib]
      rw [hzero, sub_zero] at hsub
      simpa only [finiteDifference_succ] using ha.symm.trans hsub.symm

theorem finite_martingale_terminal_pairing
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {G : ℕ → Ω → E →L[ℝ] ℝ} {N : ℕ}
    (hG : F.IsMartingaleUpTo μ G N) (f : Ω → E) :
    μ.expect (fun ω => G N ω (f ω)) =
      ∑ j ∈ Finset.range (N + 1), μ.expect (fun ω =>
        finiteDifference G j ω (finiteDifference (F.conditionalProcess μ f) j ω)) := by
  calc
    μ.expect (fun ω => G N ω (f ω)) =
        μ.expect (fun ω => (∑ j ∈ Finset.range (N + 1),
          finiteDifference G j ω) (f ω)) := by
      congr 1
      funext ω
      rw [sum_finiteDifference_eq]
    _ = ∑ j ∈ Finset.range (N + 1),
        μ.expect (fun ω => finiteDifference G j ω (f ω)) := by
      simp only [FiniteLaw.expect, sum_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact finite_martingale_difference_pairing hG f (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hj))

end MarkovSuperreflexivity

end

end OAI
