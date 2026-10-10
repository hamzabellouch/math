import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import OAI.Analysis.MarkovType.FiniteConditionalAverage
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def finiteSelectedValue (N : ℕ) (d : ℕ → Ω → E) (σ : Ω → ℕ) (ω : Ω) : E :=
  if σ ω ≤ N then d (σ ω) ω else 0

omit sectionFintypeΩ sectionNormedSpaceℝE in
theorem finiteSelectedValue_eq_sum [Fintype Ω] [NormedSpace ℝ E] (N : ℕ) (d : ℕ → Ω → E) (σ : Ω → ℕ)
    (hpos : ∀ ω, 0 < σ ω) (ω : Ω) :
    finiteSelectedValue N d σ ω =
      ∑ n ∈ Finset.Icc 1 N, if σ ω = n then d n ω else 0 := by
  classical
  by_cases hle : σ ω ≤ N
  · have hmem : σ ω ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (hpos ω), hle⟩
    rw [finiteSelectedValue, ite_eq_left hle]
    symm
    rw [Finset.sum_eq_single (σ ω)]
    · simp
    · intro n _ hne
      simp only [ite_eq_right (Ne.symm hne)]
    · intro hnot
      exact (hnot hmem).elim
  · rw [finiteSelectedValue, ite_eq_right hle]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hne : σ ω ≠ n := by
      intro heq
      exact hle (heq.symm ▸ (Finset.mem_Icc.mp hn).2)
    simp only [ite_eq_right hne]

theorem HasZeroConditionalSum.vexpect_eq_zero {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) : μ.vexpect f = 0 := by
  classical
  let : Fintype (Quotient P) := Quotient.fintype P
  let key : Ω → Quotient P := Quotient.mk P
  have hzero : ∀ a : Quotient P, μ.fiberSum key f a = 0 := by
    intro a
    refine Quotient.inductionOn a ?_
    intro b
    simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, key, Quotient.eq,
      ite_smul, zero_smul] using hf b
  simpa only [one_smul] using μ.vexpect_key_smul_eq_zero key f hzero (fun _ => 1)

namespace FinitePartitionFiltration

theorem finiteSelectedValue_zero_conditionalSum (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (N : ℕ) (d : ℕ → Ω → E) (τ σ : Ω → ℕ)
    (hτ : F.IsStoppingTime τ) (hσ : F.IsPredictableTime σ)
    (hpos : ∀ ω, 0 < σ ω)
    (hstrict : ∀ ω, σ ω ≤ N → τ ω < σ ω)
    (hzero : ∀ n : ℕ, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (d n)) :
    HasZeroConditionalSum μ (F.stoppedSetoid τ) (finiteSelectedValue N d σ) := by
  classical
  intro a
  calc
    (∑ ω, if (F.stoppedSetoid τ).r ω a then
        μ.mass ω • finiteSelectedValue N d σ ω else 0) =
        ∑ ω, ∑ n ∈ Finset.Icc 1 N,
          if (F.stoppedSetoid τ).r ω a ∧ σ ω = n then μ.mass ω • d n ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [finiteSelectedValue_eq_sum N d σ hpos ω]
      by_cases ha : (F.stoppedSetoid τ).r ω a
      · simp only [ha, ite_true, true_and, Finset.smul_sum, smul_ite, smul_zero]
      · simp only [ha, false_and, ite_false, Finset.sum_const_zero]
    _ = ∑ n ∈ Finset.Icc 1 N,
        μ.vexpect (fun ω =>
          if (F.stoppedSetoid τ).r ω a ∧ σ ω = n then d n ω else 0) := by
      rw [Finset.sum_comm]
      simp only [FiniteLaw.vexpect, smul_ite, smul_zero]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      have hbefore : ∀ ω, σ ω = n → τ ω < n := by
        intro ω heq
        have hle : σ ω ≤ N := by simpa only [heq] using hnN
        simpa only [heq] using hstrict ω hle
      have hcancel := (hzero n hnpos hnN).indicator
        (fun ω => (F.stoppedSetoid τ).r ω a ∧ σ ω = n) (by
          intro ω η hωη
          exact F.stopped_atom_and_predictable_eq hτ hσ a hnpos hbefore hωη)
      have hdec :
          (fun ω => if (F.stoppedSetoid τ).r ω a ∧ σ ω = n then d n ω else 0) =
          (fun ω => @ite E ((F.stoppedSetoid τ).r ω a ∧ σ ω = n)
            (Classical.propDecidable _) (d n ω) 0) := by
        funext ω
        by_cases h : (F.stoppedSetoid τ).r ω a ∧ σ ω = n
        · simp only [ite_eq_left h]
        · simp only [ite_eq_right h]
      rw [hdec]
      exact hcancel.vexpect_eq_zero

omit sectionFintypeΩ sectionNormedSpaceℝE in
theorem finiteSelectedValue_adapted_stopped [Fintype Ω] [NormedSpace ℝ E] (F : FinitePartitionFiltration Ω)
    (N : ℕ) (d : ℕ → Ω → E) (σ : Ω → ℕ)
    (hpos : ∀ ω, 0 < σ ω)
    (hadapt : ∀ n : ℕ, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    {ω η : Ω} (hωη : (F.stoppedSetoid σ).r ω η) :
    finiteSelectedValue N d σ ω = finiteSelectedValue N d σ η := by
  by_cases hle : σ ω ≤ N
  · have hleη : σ η ≤ N := hωη.1 ▸ hle
    simp only [finiteSelectedValue, ite_eq_left hle, ite_eq_left hleη]
    rw [← hωη.1]
    exact hadapt (σ ω) (hpos ω) hle hωη.2
  · have hleη : ¬σ η ≤ N := by simpa only [← hωη.1] using hle
    simp only [finiteSelectedValue, ite_eq_right hle, ite_eq_right hleη]

def selectedFiltration (F : FinitePartitionFiltration Ω) (τ : ℕ → Ω → ℕ)
    (hstop : ∀ i, F.IsStoppingTime (τ i))
    (hmono : ∀ ω, Monotone (fun i => τ i ω)) : FinitePartitionFiltration Ω where
  part i := F.stoppedSetoid (τ i)
  refines := by
    intro i j hij ω η hωη
    exact F.stoppedSetoid_refines (hstop i) (fun ω => hmono ω hij) hωη

end FinitePartitionFiltration

def finiteSelectedProcess (N : ℕ) (d : ℕ → Ω → E) (τ : ℕ → Ω → ℕ)
    (j : ℕ) (ω : Ω) : E :=
  ∑ i ∈ Finset.range j, finiteSelectedValue N d (τ (i + 1)) ω

omit sectionFintypeΩ sectionNormedSpaceℝE in
@[simp] theorem finiteSelectedProcess_zero [Fintype Ω] [NormedSpace ℝ E] (N : ℕ) (d : ℕ → Ω → E)
    (τ : ℕ → Ω → ℕ) (ω : Ω) : finiteSelectedProcess N d τ 0 ω = 0 := by
  simp [finiteSelectedProcess]

@[simp] theorem finiteDifference_selectedProcess_succ (N : ℕ) (d : ℕ → Ω → E)
    (τ : ℕ → Ω → ℕ) (j : ℕ) (ω : Ω) :
    finiteDifference (finiteSelectedProcess N d τ) (j + 1) ω =
      finiteSelectedValue N d (τ (j + 1)) ω := by
  rw [finiteDifference_succ]
  simp only [finiteSelectedProcess, Finset.sum_range_succ]
  abel

namespace FinitePartitionFiltration

theorem finiteSelectedProcess_adapted (F : FinitePartitionFiltration Ω)
    (N : ℕ) (d : ℕ → Ω → E) (τ : ℕ → Ω → ℕ)
    (hstop : ∀ i, F.IsStoppingTime (τ i))
    (hmono : ∀ ω, Monotone (fun i => τ i ω))
    (hpos : ∀ i ω, 0 < τ (i + 1) ω)
    (hadapt : ∀ n : ℕ, 0 < n → n ≤ N → F.AdaptedAt n (d n)) (j : ℕ) :
    (F.selectedFiltration τ hstop hmono).AdaptedAt j (finiteSelectedProcess N d τ j) := by
  intro ω η hωη
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i + 1 ≤ j := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hrel : (F.stoppedSetoid (τ (i + 1))).r ω η :=
    F.stoppedSetoid_refines (hstop (i + 1)) (fun ν => hmono ν hij) hωη
  exact F.finiteSelectedValue_adapted_stopped N d (τ (i + 1)) (hpos i) hadapt hrel

theorem finiteSelectedProcess_isMartingaleUpTo (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (N : ℕ) (d : ℕ → Ω → E) (τ : ℕ → Ω → ℕ)
    (hstop : ∀ i, F.IsStoppingTime (τ i))
    (hmono : ∀ ω, Monotone (fun i => τ i ω))
    (hpred : ∀ i, F.IsPredictableTime (τ (i + 1)))
    (hpos : ∀ i ω, 0 < τ (i + 1) ω)
    (hstrict : ∀ i ω, τ (i + 1) ω ≤ N → τ i ω < τ (i + 1) ω)
    (hadapt : ∀ n : ℕ, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n : ℕ, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (d n)) (J : ℕ) :
    (F.selectedFiltration τ hstop hmono).IsMartingaleUpTo μ
      (finiteSelectedProcess N d τ) J := by
  constructor
  · intro j _
    exact F.finiteSelectedProcess_adapted N d τ hstop hmono hpos hadapt j
  · intro j hj _
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    have hdiff : finiteDifference (finiteSelectedProcess N d τ) (i + 1) =
        finiteSelectedValue N d (τ (i + 1)) :=
      funext (finiteDifference_selectedProcess_succ N d τ i)
    change HasZeroConditionalSum μ (F.stoppedSetoid (τ ((i + 1) - 1)))
      (finiteDifference (finiteSelectedProcess N d τ) (i + 1))
    rw [Nat.add_sub_cancel, hdiff]
    exact F.finiteSelectedValue_zero_conditionalSum μ N d (τ i) (τ (i + 1))
      (hstop i) (hpred i) (hpos i) (hstrict i) hzero

end FinitePartitionFiltration

end MarkovSuperreflexivity

end

end OAI
