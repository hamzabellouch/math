import OAI.NumberTheory.Ostmann.Construction.SelectedConstituentWord
import OAI.NumberTheory.Ostmann.Construction.ScaledWordLeaves
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors

namespace OAI

/-! # Averaging the selected-prime energy under every original constituent prior -/

namespace Ostmann
open scoped BigOperators Classical

theorem wordLeafAssignment_map {I A B : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) (f : A → B) :
    (fun v => f (wordLeafAssignment role i hi n y x v)) =
      wordLeafAssignment role i hi n (fun v => f (y v)) (fun t => f (x t)) := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t => simp only [wordLeafPartition_leaf, wordLeafAssignment_leaf]
  | inr v => simp only [wordLeafPartition_outside, wordLeafAssignment_outside]

noncomputable def constituentWordLeafBase {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n → ℕ) :
    CopyScheduleAtoms role n → ℕ :=
  fun a => ((scheduleConstituentWord role size n a).map
    (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y (fun _ => 1))).prod

theorem constituent_wordLeaf_scale {I : Type*}
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (y : WordLeafOutside (fun j : Σ a, Fin (size a) => role j.1) i hi n → ℕ)
    (x : TreeLeafIndex n → ℕ) :
    (fun a => ((scheduleConstituentWord role size n a).map
      (wordLeafAssignment (fun j : Σ a, Fin (size a) => role j.1) i hi n y x)).prod) =
      wordLeafScale role i.1 hi n (constituentWordLeafBase role size i hi n y) x :=
  grouped_wordLeaf_assignment role size i hi n y x

/-- Fixing all other constituent primes and applying a uniform selected-leaf
bound costs no factor. The measure is exactly the original product measure. -/
theorem constituent_energy_transport {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (i : Σ a, Fin (size a)) (hi : role i.1 = .word) (n : ℕ)
    (P : Finset ℕ) (cells : (Σ a, Fin (size a)) → Finset ℕ)
    (hsub : ∀ j, cells j ⊆ P) (hmass : ∀ j, (∑ p ∈ cells j, (p : ℝ)⁻¹) ≠ 0)
    (F : D → (CopyScheduleAtoms role n → ℕ) → ℝ) (B : ℝ)
    (hsection : ∀ base : CopyScheduleAtoms role n → ℕ,
      (∑ d, ∑ x : TreeLeafIndex n → P, (∏ t, primeSubsetPrior P (cells i) (x t)) *
        F d (wordLeafScale role i.1 hi n base (fun t => (x t : ℕ)))) ≤ B) :
    (∑ d, ∑ q : SurvivingConstituent role size n → P,
      scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) n
        (fun j => primeSubsetPrior P (cells j)) q *
        F d (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod)) ≤ B := by
  apply scheduled_wordLeaf_sum_le (fun j : Σ a, Fin (size a) => role j.1) i hi n
    (fun j => primeSubsetPrior P (cells j))
    (fun j => primeSubsetPrior_nonneg P (cells j))
    (fun j => primeSubsetPrior_mass P (cells j) (hsub j) (hmass j))
  intro y
  have hb := hsection (constituentWordLeafBase role size i hi n (fun v => (y v : ℕ)))
  convert hb using 1
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  have he := wordLeafAssignment_map (fun j : Σ a, Fin (size a) => role j.1) i hi n y x
    (fun q : P => (q : ℕ))
  simp_rw [congrFun he]
  exact constituent_wordLeaf_scale role size i hi n (fun v => (y v : ℕ)) (fun t => (x t : ℕ))

end Ostmann

end OAI
