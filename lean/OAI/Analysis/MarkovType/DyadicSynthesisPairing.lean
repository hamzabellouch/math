import OAI.Analysis.MarkovType.FiniteMartingalePairing
import OAI.Analysis.MarkovType.FiniteMartingaleConditional
import OAI.Analysis.MarkovType.FiniteDyadicMartingale

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_martingale_terminal_pairing_of_martingales
    {Ω : Type*} [Fintype Ω] {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {G : ℕ → Ω → E →L[ℝ] ℝ} {M : ℕ → Ω → E} {N : ℕ}
    (hG : F.IsMartingaleUpTo μ G N) (hM : F.IsMartingaleUpTo μ M N) :
    μ.expect (fun ω => G N ω (M N ω)) =
      ∑ j ∈ Finset.range (N + 1),
        μ.expect (fun ω => finiteDifference G j ω (finiteDifference M j ω)) := by
  classical
  rw [finite_martingale_terminal_pairing hG (M N)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdiff (ω : Ω) (hω : 0 < μ.mass ω) :
      finiteDifference (F.conditionalProcess μ (M N)) j ω = finiteDifference M j ω := by
    cases j with
    | zero =>
      simpa only [finiteDifference_zero, FinitePartitionFiltration.conditionalProcess] using
        hM.conditional_terminal_of_mass_pos hjN ω hω
    | succ j =>
      rw [finiteDifference_succ, finiteDifference_succ]
      change μ.conditionalAverage (Quotient.mk (F.part (j + 1))) (M N) ω -
        μ.conditionalAverage (Quotient.mk (F.part j)) (M N) ω = _
      rw [hM.conditional_terminal_of_mass_pos hjN ω hω,
        hM.conditional_terminal_of_mass_pos ((Nat.le_succ j).trans hjN) ω hω]
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hz : μ.mass ω = 0
  · simp only [hz, zero_mul]
  · exact congrArg (fun x : E => μ.mass ω * finiteDifference G j ω x)
      (hdiff ω (lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hz)))

theorem dyadicIncrement_pairing {N : ℕ} (ψ : DyadicAtom N → E →L[ℝ] ℝ)
    (φ : DyadicAtom N → E) (j : Fin N) :
    (dyadicLaw N).expect (fun ω => dyadicIncrement ψ j ω (dyadicIncrement φ j ω)) =
      (dyadicLaw j.val).expect (fun α =>
        dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
  have hpoint (ω : DyadicWord N) :
      dyadicIncrement ψ j ω (dyadicIncrement φ j ω) =
        dyadicCoefficient ψ j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))
          (dyadicCoefficient φ j (dyadicPrefix ω j.val (Nat.le_of_lt j.is_lt))) := by
    cases hb : ω j <;> simp [dyadicIncrement, dyadicSign, hb]
  simp_rw [hpoint]
  exact dyadicLaw_expect_prefix (Nat.le_of_lt j.is_lt)
    (fun α => dyadicCoefficient ψ j α (dyadicCoefficient φ j α))

theorem dyadicInputPairing_prefixes {N : ℕ} (ψ : DyadicAtom N → E →L[ℝ] ℝ)
    (φ : DyadicAtom N → E) :
    (∑ a, dyadicInputWeight a * ψ a (φ a)) =
      dyadicRoot ψ (dyadicRoot φ) + ∑ j : Fin N,
        (dyadicLaw j.val).expect (fun α =>
          dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
  classical
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma,
    dyadicInputWeight, dyadicRoot, dyadicCoefficient, FiniteLaw.expect]
  simp

theorem dyadicSynthesis_pairing {N : ℕ} (ψ : DyadicAtom N → E →L[ℝ] ℝ)
    (φ : DyadicAtom N → E) :
    (dyadicLaw N).expect (fun ω => dyadicSynthesis N ψ ω (dyadicSynthesis N φ ω)) =
      ∑ a, dyadicInputWeight a * ψ a (φ a) := by
  let f : ℕ → ℝ := fun j => (dyadicLaw N).expect (fun ω =>
    finiteDifference (dyadicProcess ψ) j ω (finiteDifference (dyadicProcess φ) j ω))
  have hz : f 0 = dyadicRoot ψ (dyadicRoot φ) := by
    simp only [f, finiteDifference_zero, dyadicProcess_zero, FiniteLaw.expect_const]
  have hs (j : Fin N) : f (j.val + 1) =
      (dyadicLaw j.val).expect (fun α =>
        dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
    simpa only [f, dyadicProcess_difference_succ, dite_eq_left j.is_lt] using
      dyadicIncrement_pairing ψ φ j
  calc
    _ = ∑ j ∈ Finset.range (N + 1), f j :=
      finite_martingale_terminal_pairing_of_martingales
        (dyadicProcess_isMartingale ψ N) (dyadicProcess_isMartingale φ N)
    _ = (∑ j : Fin N, f (j.val + 1)) + f 0 := by
      rw [Finset.sum_range_succ',
        Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k + 1)) N]
    _ = dyadicRoot ψ (dyadicRoot φ) + ∑ j : Fin N,
        (dyadicLaw j.val).expect (fun α =>
          dyadicCoefficient ψ j α (dyadicCoefficient φ j α)) := by
      simp only [hs, hz, add_comm]
    _ = _ := (dyadicInputPairing_prefixes ψ φ).symm

end MarkovSuperreflexivity

end

end OAI
