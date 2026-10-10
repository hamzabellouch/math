import OAI.NumberTheory.Ostmann.Characters.PivotEliminationActualSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.PivotEliminationActual
open Construction Preliminaries PivotProductFibers
open scoped BigOperators

theorem pivot_elimination_masked_range {Q n : ℕ} {γ : Type*} [Fintype γ]
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (ν : FinitePrior γ) (R : Finset ℕ+)
    (hR : ∀ w : PrimeTuple Q n, (∀ i, w i ∈ E i) → positiveTupleProduct w ∈ R)
    (keep : PrimeTuple Q n → γ → Prop) [∀ w y, Decidable (keep w y)]
    (G : (w : PrimeTuple Q n) → γ → ZMod (positiveTupleProduct w : ℕ) → ℂ)
    (B : γ → (P : ℕ+) → ZMod (P : ℕ) → ℂ)
    (hG : ∀ w, (∀ i, w i ∈ E i) → ∀ y, keep w y → ∀ u, ‖G w y u‖ ≤ 1) :
    ‖ν.cmean (fun y => (characterTuplePrior E hE).cmean
        (fun w => if keep w y then ∑ u, G w y u * B y (positiveTupleProduct w) u else 0))‖^2 ≤
      ((n.factorial : ℝ) * normalization E) * ν.mean (fun y => ∑ P ∈ R, ∑ u, ‖B y P u‖^2) := by
  classical
  let G' : (w : PrimeTuple Q n) → γ → ZMod (positiveTupleProduct w : ℕ) → ℂ :=
    fun w y u => if (∀ i, w i ∈ E i) ∧ keep w y then G w y u else 0
  have h := dependent_pivot_elimination_range (fun P : ℕ+ => ZMod (P : ℕ))
    (characterTuplePrior E hE) ν positiveTupleProduct R G' B
    ((n.factorial : ℝ) * normalization E)
    (fun w hw => hR w (tuple_supported_of_mass_ne_zero E hE w hw))
    (by
      intro w y u
      dsimp [G']
      split_ifs with hw
      · exact hG w hw.1 y hw.2 u
      · simp)
    (by
      intro P _
      have hh := fiber_mass_mul_residue_card_le E hE P
      simp only [Finset.sum_filter] at hh ⊢
      refine le_trans (le_of_eq ?_) hh
      apply congrArg (fun x : ℝ => x * (Fintype.card (ZMod (P : ℕ)) : ℝ))
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : positiveTupleProduct w = P <;> simp only [hw, ite_true, ite_false])
  have heq (y : γ) : (characterTuplePrior E hE).cmean
      (fun w => ∑ u, G' w y u * B y (positiveTupleProduct w) u) =
      (characterTuplePrior E hE).cmean
        (fun w => if keep w y then ∑ u, G w y u * B y (positiveTupleProduct w) u else 0) := by
    unfold FinitePrior.cmean
    apply Finset.sum_congr rfl
    intro w _
    by_cases hs : ∀ i, w i ∈ E i
    · by_cases hk : keep w y <;> simp [G', hs, hk]
    · have hz := characterTuplePrior_mass_eq_zero E hE w hs
      simp [hz]
  simpa only [heq] using h

theorem pivot_elimination_masked {Q n : ℕ} {γ : Type*} [Fintype γ]
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (ν : FinitePrior γ)
    (keep : PrimeTuple Q n → γ → Prop) [∀ w y, Decidable (keep w y)]
    (G : (w : PrimeTuple Q n) → γ → ZMod (positiveTupleProduct w : ℕ) → ℂ)
    (B : γ → (P : ℕ+) → ZMod (P : ℕ) → ℂ)
    (hG : ∀ w, (∀ i, w i ∈ E i) → ∀ y, keep w y → ∀ u, ‖G w y u‖ ≤ 1) :
    ‖ν.cmean (fun y => (characterTuplePrior E hE).cmean
        (fun w => if keep w y then ∑ u, G w y u * B y (positiveTupleProduct w) u else 0))‖^2 ≤
      ((n.factorial : ℝ) * normalization E) *
        ν.mean (fun y => ∑ P ∈ positiveProductRange E, ∑ u, ‖B y P u‖^2) :=
  pivot_elimination_masked_range E hE ν (positiveProductRange E)
    (fun w hw => (mem_positiveProductRange E _).mpr ⟨w, hw, rfl⟩) keep G B hG

theorem pivot_elimination {Q n : ℕ} {γ : Type*} [Fintype γ]
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (ν : FinitePrior γ)
    (G : (w : PrimeTuple Q n) → γ → ZMod (positiveTupleProduct w : ℕ) → ℂ)
    (B : γ → (P : ℕ+) → ZMod (P : ℕ) → ℂ)
    (hG : ∀ w, (∀ i, w i ∈ E i) → ∀ y u, ‖G w y u‖ ≤ 1) :
    ‖ν.cmean (fun y => (characterTuplePrior E hE).cmean
        (fun w => ∑ u, G w y u * B y (positiveTupleProduct w) u))‖^2 ≤
      ((n.factorial : ℝ) * normalization E) *
        ν.mean (fun y => ∑ P ∈ positiveProductRange E, ∑ u, ‖B y P u‖^2) := by
  classical
  simpa only [ite_true] using pivot_elimination_masked E hE ν (fun _ _ => True) G B
    (fun w hw y _ u => hG w hw y u)

theorem pivot_elimination_range {Q n : ℕ} {γ : Type*} [Fintype γ]
    (E : Fin n → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (ν : FinitePrior γ) (R : Finset ℕ+)
    (hR : ∀ w : PrimeTuple Q n, (∀ i, w i ∈ E i) → positiveTupleProduct w ∈ R)
    (G : (w : PrimeTuple Q n) → γ → ZMod (positiveTupleProduct w : ℕ) → ℂ)
    (B : γ → (P : ℕ+) → ZMod (P : ℕ) → ℂ)
    (hG : ∀ w, (∀ i, w i ∈ E i) → ∀ y u, ‖G w y u‖ ≤ 1) :
    ‖ν.cmean (fun y => (characterTuplePrior E hE).cmean
        (fun w => ∑ u, G w y u * B y (positiveTupleProduct w) u))‖^2 ≤
      ((n.factorial : ℝ) * normalization E) * ν.mean (fun y => ∑ P ∈ R, ∑ u, ‖B y P u‖^2) := by
  classical
  simpa only [ite_true] using pivot_elimination_masked_range E hE ν R hR (fun _ _ => True) G B
    (fun w hw y _ u => hG w hw y u)

end Ostmann.Characters.PivotEliminationActual

end

end OAI
