import Mathlib.Analysis.SpecificLimits.Basic
import OAI.Combinatorics.BalancedRyser.Local.LocalKernel
import OAI.Combinatorics.BalancedRyser.Local.LocalPatternEvents

namespace OAI

namespace Balanced.Local.HighReuse

universe u
open Filter
open scoped BigOperators Topology

noncomputable section
open scoped Classical

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
theorem selectedProbability_exists_le_sum {I : Type*} [Fintype I]
    (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (E : I → Configuration F → Prop) :
    selectedProbability w (fun C => ∃ i, E i C) ≤
      ∑ i, selectedProbability w (E i) := by
  unfold selectedProbability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ M : MergedPairs F, ∑ v : Output F, ∑ i : I,
        if E i (configuration M v) then w M v else 0 := by
      apply Finset.sum_le_sum
      intro M _
      apply Finset.sum_le_sum
      intro v _
      split_ifs with h
      · obtain ⟨i, hi⟩ := h
        calc
          w M v = if E i (configuration M v) then w M v else 0 := by simp [hi]
          _ ≤ _ := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun j : I => if E j (configuration M v) then w M v else 0)
            (fun j _ => by split_ifs <;> first | exact hw M v | exact le_rfl)
            (Finset.mem_univ i)
      · exact Finset.sum_nonneg (fun i _ => by
          split_ifs <;> first | exact hw M v | exact le_rfl)
    _ = _ := by
      calc
        _ = ∑ M : MergedPairs F, ∑ i : I, ∑ v : Output F,
            if E i (configuration M v) then w M v else 0 := by
          apply Finset.sum_congr rfl
          intro M _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem selected_highReuse_le (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    (C : ℝ)
    (hpoint : ∀ p : Point F,
      selectedProbability w (fun X =>
        2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) ≤
        C / (Fintype.card F : ℝ) ^ 3) :
    selectedProbability w HighReuseEvent ≤ C / Fintype.card F := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ∑ p : Point F, selectedProbability w (fun X =>
        2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) :=
      selectedProbability_exists_le_sum w hw _
    _ ≤ ∑ _p : Point F, C / (Fintype.card F : ℝ) ^ 3 :=
      Finset.sum_le_sum (fun p _ => hpoint p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Point, Fintype.card_prod, Nat.cast_mul]
      field_simp

theorem local_failure_le_large_add_reuse_add_small
    (Q : RetentionRule F) (w : Kernel F) (K C : ℝ)
    (hw : KernelConditions Q w K)
    (hpoint : ∀ p : Point F,
      selectedProbability w (fun X =>
        2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) ≤
        C / (Fintype.card F : ℝ) ^ 3) :
    selectedProbability w (fun X => ¬ X.LocalCondition) ≤
      selectedProbability w LargePencilEvent + C / Fintype.card F +
        selectedProbability w SmallBadPatternEvent := by
  apply (local_failure_probability_le Q w K hw).trans
  exact add_le_add (add_le_add le_rfl
    (selected_highReuse_le w hw.1 C hpoint)) le_rfl

theorem uniform_vanishing_of_pencilReuse (hreuse : PencilReuseResult.{u}) :
    ∀ K : ℝ, 0 < K → ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (𝓝 0) ∧ (∀ q, 0 ≤ ε q) ∧
      ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
        KernelConditions Q w K → selectedProbability w HighReuseEvent ≤
          ε (Fintype.card F) := by
  intro K hK
  obtain ⟨C, hC, q₀, hbound⟩ := hreuse K hK
  refine ⟨fun q => C / (q : ℝ), tendsto_const_div_atTop_nhds_zero_nat C,
    (fun q => div_nonneg hC.le (Nat.cast_nonneg q)), q₀, ?_⟩
  intro F _ _ _ hq Q w hw
  exact selected_highReuse_le w hw.1 C (hbound F hq Q w hw)

end
end Balanced.Local.HighReuse

end OAI
