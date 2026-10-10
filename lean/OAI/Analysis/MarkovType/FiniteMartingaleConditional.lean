import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import OAI.Analysis.MarkovType.FiniteConditionalAverage
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasZeroConditionalSum.sum_indicator {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (A : Ω → Prop)
    (hA : ∀ {ω η}, P.r ω η → (A ω ↔ A η)) :
    (∑ ω, if A ω then μ.mass ω • f ω else 0) = 0 := by
  classical
  let key : Ω → Quotient P := Quotient.mk P
  let B : Quotient P → Prop := Quotient.lift A (fun _ _ h => propext (hA h))
  have hzero (a : Quotient P) : μ.fiberSum key f a = 0 := by
    refine Quotient.inductionOn a ?_
    intro a
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, key,
      Quotient.eq, ite_smul, zero_smul] using hf a
  have h := μ.vexpect_key_indicator_eq_zero key f hzero B
  change (∑ ω, μ.mass ω • (if A ω then f ω else 0)) = 0 at h
  simpa only [smul_ite, smul_zero] using h

theorem HasZeroConditionalSum.of_refinement {μ : FiniteLaw Ω}
    {P Q : Setoid Ω} {f : Ω → E} (hf : HasZeroConditionalSum μ Q f)
    (hPQ : ∀ {ω η}, Q.r ω η → P.r ω η) : HasZeroConditionalSum μ P f := by
  intro a
  apply hf.sum_indicator (fun ω => P.r ω a)
  intro ω η hωη
  have hp := hPQ hωη
  exact ⟨fun h => P.trans' (P.symm' hp) h, fun h => P.trans' hp h⟩

namespace FinitePartitionFiltration

variable {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
variable {M : ℕ → Ω → E} {N : ℕ}

theorem IsMartingaleUpTo.terminal_atom_sum (hM : F.IsMartingaleUpTo μ M N)
    {j : ℕ} (hj : j ≤ N) (a : Ω) :
    (∑ ω, if (F.part j).r ω a then μ.mass ω • M N ω else 0) =
      ∑ ω, if (F.part j).r ω a then μ.mass ω • M j ω else 0 := by
  classical
  have haux : ∀ n : ℕ, j ≤ n → n ≤ N →
      (∑ ω, if (F.part j).r ω a then μ.mass ω • M n ω else 0) =
        ∑ ω, if (F.part j).r ω a then μ.mass ω • M j ω else 0 := by
    intro n
    induction n with
    | zero =>
      intro hjn hnN
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjn
      subst j
      rfl
    | succ n ih =>
      intro hjn hnN
      by_cases heq : j = n + 1
      · subst j
        rfl
      · have hjn' : j ≤ n := by omega
        have hnn : n ≤ N := (Nat.le_succ n).trans hnN
        have hz : HasZeroConditionalSum μ (F.part n)
            (finiteDifference M (n + 1)) := by
          simpa only [Nat.add_sub_cancel] using hM.2 (n + 1) (Nat.succ_pos n) hnN
        have hz' : HasZeroConditionalSum μ (F.part j)
            (finiteDifference M (n + 1)) :=
          hz.of_refinement (fun {_ _} h => F.refines hjn' h)
        have hstep := hz' a
        have hdiff :
            (∑ ω, if (F.part j).r ω a then μ.mass ω • M (n + 1) ω else 0) -
              (∑ ω, if (F.part j).r ω a then μ.mass ω • M n ω else 0) = 0 := by
          calc
            _ = ∑ ω, if (F.part j).r ω a then
                μ.mass ω • (M (n + 1) ω - M n ω) else 0 := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro ω _
              by_cases h : (F.part j).r ω a <;> simp only [h, ite_true, ite_false,
                smul_sub, sub_zero]
            _ = 0 := by simpa only [finiteDifference_succ] using hstep
        exact (sub_eq_zero.mp hdiff).trans (ih hjn' hnn)
  exact haux N hj le_rfl

omit sectionFintypeΩ in
theorem stopped_rel_iff_at_time [Fintype Ω] {τ : Ω → ℕ} (hτ : F.IsStoppingTime τ)
    (ω a : Ω) : (F.stoppedSetoid τ).r ω a ↔ (F.part (τ a)).r ω a := by
  constructor
  · intro h
    rw [← h.1]
    exact h.2
  · intro h
    exact (F.stoppedSetoid τ).symm'
      (F.stopped_rel_of_rel_of_le hτ ((F.part (τ a)).symm' h) le_rfl)

theorem IsMartingaleUpTo.stopped_atom_sum (hM : F.IsMartingaleUpTo μ M N)
    {τ : Ω → ℕ} (hτ : F.IsStoppingTime τ) (hτN : ∀ ω, τ ω ≤ N) (a : Ω) :
    (∑ ω, if (F.stoppedSetoid τ).r ω a then μ.mass ω • M N ω else 0) =
      (∑ ω, if (F.stoppedSetoid τ).r ω a then μ.mass ω else 0) • M (τ a) a := by
  classical
  simp only [stopped_rel_iff_at_time hτ]
  rw [hM.terminal_atom_sum (hτN a) a, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : (F.part (τ a)).r ω a
  · simp only [ite_eq_left h, hM.1 (τ a) (hτN a) h]
  · simp only [ite_eq_right h, zero_smul]

theorem IsMartingaleUpTo.conditional_terminal_stopped_of_mass_pos
    (hM : F.IsMartingaleUpTo μ M N) {τ : Ω → ℕ}
    (hτ : F.IsStoppingTime τ) (hτN : ∀ ω, τ ω ≤ N)
    (ω : Ω) (hω : 0 < μ.mass ω) :
    μ.conditionalAverage (Quotient.mk (F.stoppedSetoid τ)) (M N) ω = M (τ ω) ω := by
  classical
  let key := Quotient.mk (F.stoppedSetoid τ)
  have hmass : 0 < μ.fiberMass key (key ω) := μ.fiberMass_pos_of_mass_pos key hω
  have hsum : μ.fiberSum key (M N) (key ω) =
      μ.fiberMass key (key ω) • M (τ ω) ω := by
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberMass, FiniteLaw.fiberWeight,
      key, Quotient.eq, ite_smul, zero_smul] using hM.stopped_atom_sum hτ hτN ω
  change (μ.fiberMass key (key ω))⁻¹ • μ.fiberSum key (M N) (key ω) = _
  rw [hsum, smul_smul, inv_mul_cancel₀ hmass.ne', one_smul]

theorem IsMartingaleUpTo.conditional_terminal_of_mass_pos
    (hM : F.IsMartingaleUpTo μ M N) {j : ℕ} (hj : j ≤ N)
    (ω : Ω) (hω : 0 < μ.mass ω) :
    μ.conditionalAverage (Quotient.mk (F.part j)) (M N) ω = M j ω := by
  classical
  let key := Quotient.mk (F.part j)
  have hmass : 0 < μ.fiberMass key (key ω) := μ.fiberMass_pos_of_mass_pos key hω
  have hsum : μ.fiberSum key (M N) (key ω) =
      μ.fiberMass key (key ω) • M j ω := by
    simp only [FiniteLaw.fiberSum, FiniteLaw.fiberMass, FiniteLaw.fiberWeight,
      key, Quotient.eq, ite_smul, zero_smul]
    rw [hM.terminal_atom_sum hj ω, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro η _
    by_cases h : (F.part j).r η ω
    · simp only [ite_eq_left h, hM.1 j hj h]
    · simp only [ite_eq_right h, zero_smul]
  change (μ.fiberMass key (key ω))⁻¹ • μ.fiberSum key (M N) (key ω) = _
  rw [hsum, smul_smul, inv_mul_cancel₀ hmass.ne', one_smul]

theorem IsMartingaleUpTo.expect_stopped_norm_sq_le
    (hM : F.IsMartingaleUpTo μ M N) {τ : Ω → ℕ}
    (hτ : F.IsStoppingTime τ) (hτN : ∀ ω, τ ω ≤ N) :
    μ.expect (fun ω => ‖M (τ ω) ω‖ ^ (2 : ℕ)) ≤
      μ.expect (fun ω => ‖M N ω‖ ^ (2 : ℕ)) := by
  classical
  let key := Quotient.mk (F.stoppedSetoid τ)
  calc
    μ.expect (fun ω => ‖M (τ ω) ω‖ ^ (2 : ℕ)) =
        μ.expect (fun ω => ‖μ.conditionalAverage key (M N) ω‖ ^ (2 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hzero : μ.mass ω = 0
      · simp only [hzero, zero_mul]
      · have hpos := lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hzero)
        change μ.mass ω * ‖M (τ ω) ω‖ ^ (2 : ℕ) =
          μ.mass ω * ‖μ.conditionalAverage (Quotient.mk (F.stoppedSetoid τ)) (M N) ω‖ ^ (2 : ℕ)
        rw [hM.conditional_terminal_stopped_of_mass_pos hτ hτN ω hpos]
    _ ≤ _ := by
      simpa only [Real.rpow_two] using
        μ.expect_norm_conditionalAverage_rpow_le key (M N) (q := (2 : ℝ)) (by norm_num)

end FinitePartitionFiltration

end MarkovSuperreflexivity

end

end OAI
