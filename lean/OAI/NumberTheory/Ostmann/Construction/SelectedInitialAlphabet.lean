import OAI.NumberTheory.Ostmann.Construction.InitialAmplitudeAlphabet
import OAI.NumberTheory.Ostmann.Construction.InitialCellPriors
import OAI.NumberTheory.Ostmann.Construction.InitialMovingAverage
import OAI.NumberTheory.Ostmann.Construction.SelectedCompensationPrior

namespace OAI

/-! # Every live selected regular prime belongs to the small alphabet -/
namespace Ostmann
open scoped Classical

theorem list_headD_drop_get {α : Type*} (xs : List α) (fallback : α)
    (j : ℕ) (hj : j < xs.length) :
    (xs.drop j).headD fallback = xs.get ⟨j, hj⟩ := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [List.drop_succ_cons, List.get_cons_succ] using ih j (by simpa using hj)

theorem initialMovingRegularPrior_support {P : Type*} (b r : ℕ)
    (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ) (S : Set P)
    (hb : ∀ i p, μb i p ≠ 0 → p ∈ S)
    (hc : ∀ i p, μc i p ≠ 0 → p ∈ S)
    (i : MovingRegularSlot 0 (r + r) (b + b)) (p : P)
    (hp : initialMovingRegularPrior b r μb μc i p ≠ 0) : p ∈ S := by
  rcases i with ⟨u, i | i⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i hp
    · simpa only [initialMovingRegularPrior, Sum.elim_inl, Fin.append_left] using hc j p
    · simpa only [initialMovingRegularPrior, Sum.elim_inl, Fin.append_right] using hc j p
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i hp
    · simpa only [initialMovingRegularPrior, Sum.elim_inr, Fin.append_left] using hb j p
    · simpa only [initialMovingRegularPrior, Sum.elim_inr, Fin.append_right] using hb j p

theorem selected_initial_regular_alphabet
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D Qb : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hsmall : initialRegularPrimeRange L ⊆ P)
    (hbulk : Qb ⊆ initialRegularPrimeRange L) (b : ℕ) :
    let cells := initialSmallCellList top centers
    let μb := fun _ : Fin b => primeSubsetPrior P Qb
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y hi D (cells.get i))
    ∀ i p, initialMovingRegularPrior b cells.length μb μc i p ≠ 0 →
      p ∈ Set.range (primeAlphabetEmbedding hsmall) := by
  intro cells μb μc
  apply initialMovingRegularPrior_support
  · intro i p hp
    exact primeSubsetPrior_alphabet_support hsmall hbulk p hp
  · intro i p hp
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcenters _ (List.get_mem cells i)
    exact primeSubsetPrior_alphabet_support hsmall ht.subset_initialRegularPrimeRange p hp

theorem selected_compensation_alphabet
    {A B : Set ℕ} {N hi : ℕ} {a C L Y : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets)
    (P : Finset ℕ) (hsmall : initialRegularPrimeRange L ⊆ P)
    (j : ℕ) (hj : j < centers.length) (p : P)
    (hp : selectedCompensationPrior A B N Y hi D P centers j p ≠ 0) :
    p ∈ Set.range (primeAlphabetEmbedding hsmall) := by
  have hdrop := list_headD_drop_get centers 0 j hj
  have hj' : j < targets.length := hcenters.length_eq ▸ hj
  have hc := hcenters.get hj hj'
  apply primeSubsetPrior_alphabet_support
    (S := selectedTailCellPrimes A B N Y hi D ((centers.drop j).headD 0)) hsmall
  · rw [hdrop]
    exact hc.subset_initialRegularPrimeRange
  · exact hp

end Ostmann

end OAI
