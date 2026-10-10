import OAI.Computability.DepthThree.MachineLanguage
import OAI.Computability.DepthThree.LanguageLowerBound

namespace OAI

namespace DepthThreeLowerBound

theorem exists_polynomial_time_language_depth_three_lower_bound :
    ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ),
      0 < C ∧ 0 < a ∧
      (∀ w : List Bool, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) →
          (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (D.gateCount : ℝ) := by
  obtain ⟨M, C, a, hC, ha, hM⟩ := language_polynomial_time
  exact ⟨language, M, C, a, hC, ha, hM, language_depth_three_gate_lower_bound⟩

end DepthThreeLowerBound

end OAI
