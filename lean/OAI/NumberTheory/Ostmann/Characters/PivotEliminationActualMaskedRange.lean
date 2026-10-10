import OAI.NumberTheory.Ostmann.Characters.PivotEliminationActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.PivotEliminationActual
open Construction Preliminaries PivotProductFibers
open scoped BigOperators

theorem pivot_elimination_masked_subrange {Q n : ℕ} {γ : Type*} [Fintype γ]
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (ν : FinitePrior γ) (R : Finset ℕ+)
    (keep : PrimeTuple Q n → γ → Prop) [∀ w y, Decidable (keep w y)]
    (hR : ∀ w : PrimeTuple Q n, (∀ i, w i ∈ E i) → ∀ y,
      keep w y → positiveTupleProduct w ∈ R)
    (G : (w : PrimeTuple Q n) → γ → ZMod (positiveTupleProduct w : ℕ) → ℂ)
    (B : γ → (P : ℕ+) → ZMod (P : ℕ) → ℂ)
    (hG : ∀ w, (∀ i, w i ∈ E i) → ∀ y, keep w y → ∀ u, ‖G w y u‖ ≤ 1) :
    ‖ν.cmean (fun y => (characterTuplePrior E hE).cmean
        (fun w => if keep w y then ∑ u, G w y u * B y (positiveTupleProduct w) u else 0))‖^2 ≤
      ((n.factorial : ℝ) * normalization E) * ν.mean (fun y => ∑ P ∈ R, ∑ u, ‖B y P u‖^2) := by
  classical
  let B' : γ → (P : ℕ+) → ZMod (P : ℕ) → ℂ :=
    fun y P u => if P ∈ R then B y P u else 0
  have h := pivot_elimination_masked E hE ν keep G B' hG
  have heq (y : γ) : (characterTuplePrior E hE).cmean
      (fun w => if keep w y then ∑ u, G w y u * B' y (positiveTupleProduct w) u else 0) =
      (characterTuplePrior E hE).cmean
        (fun w => if keep w y then ∑ u, G w y u * B y (positiveTupleProduct w) u else 0) := by
    unfold FinitePrior.cmean
    apply Finset.sum_congr rfl
    intro w _
    by_cases hs : ∀ i, w i ∈ E i
    · by_cases hk : keep w y
      · simp only [B', ite_eq_left hk, ite_eq_left (hR w hs y hk)]
      · simp only [ite_eq_right hk]
    · have hz := characterTuplePrior_mass_eq_zero E hE w hs
      simp [hz]
  have henergy (y : γ) :
      (∑ P ∈ positiveProductRange E, ∑ u, ‖B' y P u‖^2) ≤ ∑ P ∈ R, ∑ u, ‖B y P u‖^2 := by
    calc
      _ = ∑ P ∈ (positiveProductRange E).filter (fun P => P ∈ R), ∑ u, ‖B y P u‖^2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro P _
        by_cases hP : P ∈ R <;> simp [B', hP]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun P hP => (Finset.mem_filter.mp hP).2)
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hfirst :
      ‖ν.cmean (fun y => (characterTuplePrior E hE).cmean
        (fun w => if keep w y then ∑ u, G w y u * B y (positiveTupleProduct w) u else 0))‖^2 ≤
      ((n.factorial : ℝ) * normalization E) *
        ν.mean (fun y => ∑ P ∈ positiveProductRange E, ∑ u, ‖B' y P u‖^2) := by
    simpa only [heq] using h
  exact hfirst.trans (mul_le_mul_of_nonneg_left (ν.mean_mono henergy)
    (mul_nonneg (Nat.cast_nonneg _) (normalization_nonneg E hE)))

end Ostmann.Characters.PivotEliminationActual

end

end OAI
