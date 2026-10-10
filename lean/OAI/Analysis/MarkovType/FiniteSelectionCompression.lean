import OAI.Analysis.MarkovType.FinitePredictableSelection
import OAI.Analysis.MarkovType.FiniteSelectionCounter

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

def selectionProcess (N : ℕ) (B : ℕ → Ω → Prop) (d : ℕ → Ω → E) : ℕ → Ω → E :=
  finiteSelectedProcess N d (selectionTime N B)

@[simp] theorem selectionProcess_zero (N : ℕ) (B : ℕ → Ω → Prop)
    (d : ℕ → Ω → E) (ω : Ω) : selectionProcess N B d 0 ω = 0 := by
  exact finiteSelectedProcess_zero N d (selectionTime N B) ω

@[simp] theorem finiteDifference_selectionProcess_succ (N : ℕ)
    (B : ℕ → Ω → Prop) (d : ℕ → Ω → E) (i : ℕ) (ω : Ω) :
    finiteDifference (selectionProcess N B d) (i + 1) ω =
      if selectionSlot N B i ω ≤ N then d (selectionSlot N B i ω) ω else 0 := by
  exact finiteDifference_selectedProcess_succ N d (selectionTime N B) i ω

omit sectionFintypeΩ sectionNormedSpaceℝE in
theorem selectionProcess_eq_sum [Fintype Ω] [NormedSpace ℝ E] (N : ℕ) (B : ℕ → Ω → Prop)
    (d : ℕ → Ω → E) (J : ℕ) (ω : Ω) (hJ : selectionCount N B ω ≤ J) :
    selectionProcess N B d J ω =
      ∑ n ∈ Finset.Icc 1 N, if B n ω then d n ω else 0 := by
  classical
  calc
    _ = ∑ n ∈ Finset.range (N + 1),
        if selectionPredicate N B ω n then d n ω else 0 :=
      sum_selectionSlot_padded N B ω (fun n => d n ω) J hJ
    _ = ∑ n ∈ Finset.Icc 1 N,
        if selectionPredicate N B ω n then d n ω else 0 := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n hn hnot
        have hnN : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        have hnzero : n = 0 := by
          by_contra hne
          exact hnot (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, hnN⟩)
        simp only [selectionPredicate, hnzero, Nat.lt_irrefl, false_and, ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      simp only [selectionPredicate, hnpos, hnN, true_and]

theorem norm_finiteDifference_selectionProcess_le (N : ℕ) (B : ℕ → Ω → Prop)
    (d : ℕ → Ω → E) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, 0 < n → n ≤ N → ∀ ω, B n ω → ‖d n ω‖ ≤ C)
    (i : ℕ) (ω : Ω) :
    ‖finiteDifference (selectionProcess N B d) (i + 1) ω‖ ≤ C := by
  rw [finiteDifference_selectionProcess_succ]
  by_cases hle : selectionSlot N B i ω ≤ N
  · rw [ite_eq_left hle]
    have hmem := selectionSlot_mem ((selectionSlot_le_horizon_iff N i B ω).mp hle)
    exact hd (selectionSlot N B i ω) hmem.1 hmem.2.1 ω hmem.2.2
  · simpa only [ite_eq_right hle, norm_zero] using hC

namespace FinitePartitionFiltration

def selectionFiltration (F : FinitePartitionFiltration Ω) (N : ℕ)
    (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η)) : FinitePartitionFiltration Ω :=
  F.selectedFiltration (selectionTime N B)
    (selectionTime_stopping F N B hB) (selectionTime_monotone N B)

theorem selectionProcess_isMartingaleUpTo (F : FinitePartitionFiltration Ω)
    (μ : FiniteLaw Ω) (N : ℕ) (B : ℕ → Ω → Prop) (d : ℕ → Ω → E)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η))
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum μ (F.part (n - 1)) (d n)) (J : ℕ) :
    (F.selectionFiltration N B hB).IsMartingaleUpTo μ (selectionProcess N B d) J := by
  exact F.finiteSelectedProcess_isMartingaleUpTo μ N d (selectionTime N B)
    (selectionTime_stopping F N B hB) (selectionTime_monotone N B)
    (selectionSlot_predictable F N B hB) (fun i => selectionSlot_pos N i B)
    (fun i ω hi => selectionTime_strict_before_horizon B ω hi) hadapt hzero J

theorem IsMartingaleUpTo.selectionProcess {F : FinitePartitionFiltration Ω}
    {μ : FiniteLaw Ω} {M : ℕ → Ω → E} {N : ℕ}
    (hM : F.IsMartingaleUpTo μ M N) (B : ℕ → Ω → Prop)
    (hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η)) (J : ℕ) :
    (F.selectionFiltration N B hB).IsMartingaleUpTo μ
      (MarkovSuperreflexivity.selectionProcess N B (finiteDifference M)) J :=
  F.selectionProcess_isMartingaleUpTo μ N B (finiteDifference M) hB
    (fun _ _ hn => hM.difference_adapted hn) hM.2 J

end FinitePartitionFiltration

end MarkovSuperreflexivity

end

end OAI
