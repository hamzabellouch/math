import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalSplit

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem finite_guarded_sum_norm_le {α : Type*} [Fintype α] (P : α→Prop)
    (F : α→ℂ) (ε : ℝ) (hF : ∀a,P a→‖F a‖≤ε) :
    ‖∑a,if P a then F a else 0‖≤(Nat.card {a // P a}:ℝ)*ε := by
  rw [←Finset.sum_filter]
  calc
    _ ≤ ∑a∈Finset.univ.filter P,‖F a‖ := norm_sum_le _ _
    _ ≤ ∑a∈Finset.univ.filter P,ε := Finset.sum_le_sum fun a ha =>
      hF a (Finset.mem_filter.mp ha).2
    _ = _ := by simp [Nat.card_eq_fintype_card,Fintype.card_subtype]

namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem selectedGoodCovarianceSum_zero_low_level (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) (hl : l≤1) :
    C.selectedGoodCovarianceSum spectator s X l=0 := by
  have hr : 2^l≤2 := by interval_cases l <;> norm_num
  unfold selectedGoodCovarianceSum
  apply Finset.sum_eq_zero
  intro e he
  have hg : ¬diagonalGoodPermutation (2*(Conclusion.bulkSize k L/2)) k l e := by
    intro h
    exact h.2 (Or.inl hr)
  simp only [hg,ite_false]

theorem selectedGoodCovarianceSum_norm_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) (ε : ℝ)
    (hgood : ∀e,diagonalGoodPermutation (2*(Conclusion.bulkSize k L/2)) k l e →
      ‖C.selectedDiagonalCovariance spectator s X l e‖≤ε) :
    ‖C.selectedGoodCovarianceSum spectator s X l‖≤
      (Nat.card {e // diagonalGoodPermutation (2*(Conclusion.bulkSize k L/2)) k l e}:ℝ)*ε :=
  finite_guarded_sum_norm_le _ _ _ hgood

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
