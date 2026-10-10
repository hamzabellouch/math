import Mathlib

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation

theorem specified_failures {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M) (_hMle : ∀ n, M n≤‹MeasurableSpace Ω›)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (ε : ℝ) (hε : 0≤ε)
    (hcond : ∀ n B, MeasurableSet[M n] B → μ.real (B∩F n)≤ε*μ.real B)
    (s : Finset ℕ) : μ.real (⋂ n∈s, F n) ≤ ε^s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert n s hn ih =>
    have hns : n∉s := fun h => (lt_irrefl n) (hn n h)
    have hBs : MeasurableSet[M n] (⋂ j∈s, F j) := by
      apply MeasurableSet.biInter s.finite_toSet.countable
      intro j hj
      exact hM (Nat.succ_le_of_lt (hn j hj)) _ (hF j)
    have h := hcond n (⋂ j∈s, F j) hBs
    rw [Finset.set_biInter_insert,Finset.card_insert_of_notMem hns,pow_succ]
    rw [Set.inter_comm]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ih hε])

theorem specified_failures_with_initialization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B₀ : Set Ω) (hB₀ : MeasurableSet[M 0] B₀)
    (ε : ℝ) (hε : 0≤ε)
    (hcond : ∀ n B, MeasurableSet[M n] B → B⊆B₀ →
      μ.real (B∩F n)≤ε*μ.real B)
    (s : Finset ℕ) : μ.real (B₀∩⋂ n∈s, F n) ≤ μ.real B₀*ε^s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert n s hn ih =>
    have hns : n∉s := fun h => (lt_irrefl n) (hn n h)
    have hbs : MeasurableSet[M n] (B₀∩⋂ j∈s, F j) := by
      refine ((hM (Nat.zero_le n)) _ hB₀).inter ?_
      apply MeasurableSet.biInter s.finite_toSet.countable
      intro j hj
      exact hM (Nat.succ_le_of_lt (hn j hj)) _ (hF j)
    have h := hcond n (B₀∩⋂ j∈s, F j) hbs Set.inter_subset_left
    have he : B₀∩⋂ j∈insert n s, F j=(B₀∩⋂ j∈s, F j)∩F n := by
      rw [Finset.set_biInter_insert]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [he,Finset.card_insert_of_notMem hns,pow_succ]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ih hε])

end CriticalPercolation
end
end
end

end OAI
