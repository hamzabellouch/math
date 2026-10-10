import OAI.Geometry.Coboundary.LatticeCones
import OAI.Combinatorics.Coboundary.Skeleton
import OAI.GroupTheory.Congruence.FrameHomology

namespace OAI

/-!
Uniform congruence homology vanishing and the complete bounded-degree coboundary-expander theorem.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders
open Construction

/-- A single prime threshold supplies all the finitely many ambient U-ranks
needed in an inductive homology argument. -/
theorem uniform_u_homology (N : ℕ) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Odd p → Q < p →
      ∀ a : ℕ, 4 ≤ a → a ≤ N → ∀ j : ℕ, 0 < j → j < a-2 →
        IsZero (groupHomology (Rep.trivial (ZMod 2) (U p a) (ZMod 2)) j) := by
  induction N with
  | zero => exact ⟨0,fun _ _ _ _ a ha hN => by omega⟩
  | succ N ih =>
    by_cases hN : 4 ≤ N+1
    · obtain ⟨Q₁,hQ₁⟩ := ih
      obtain ⟨Q₂,hQ₂⟩ := uniform_infinite_coset_positive N (by omega)
      refine ⟨max Q₁ Q₂,?_⟩
      intro p inst hp hQ a ha haN j hj hja
      rcases lt_or_eq_of_le haN with hlt | rfl
      · exact hQ₁ p hp (lt_of_le_of_lt (le_max_left _ _) hQ) a ha (by omega) j hj hja
      · apply u_homology_isZero_of_opposition p N (by omega) hp
          ((oppositionAcyclic_iff_positive p N (by omega)).mpr
            (hQ₂ p (lt_of_le_of_lt (le_max_right _ _) hQ))) j hj
        omega
    · exact ⟨0,fun _ _ _ _ a ha haN => by omega⟩

/-- The actual congruence-group vanishing follows by induction on homological
degree, using the ordinary partial-basis edge argument and odd-index transfer.
This does not assume integral pro-stability or a stability theorem. -/
theorem gamma_vanishing_of_u (p N : ℕ) [Fact p.Prime] (hp : Odd p)
    (hU : ∀ a : ℕ, 4 ≤ a → a ≤ N → ∀ j : ℕ, 0 < j → j < a-2 →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (U p a) (ZMod 2)) j)) :
    ∀ j : ℕ, 0 < j → ∀ a : ℕ, 2*j+2 ≤ a → a ≤ N →
      ∀ m : ℕ, 1 ≤ m →
        IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj a ha haN m hm
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    apply QuotientVanishing.gamma_isZero_of_U_and_action p (a+1) m Fact.out hp hm (q+1)
    · exact hU (a+1) (by omega) haN (q+1) (by omega) (by omega)
    · intro g
      exact CongruenceFrames.conjugation_trivial p a m hm hp q ha (by
        intro t ht htq
        exact ih (q+1-t) (by omega) (by omega) (a+1-(t+1)) (by omega) (by omega) m hm) g

/-- Consequently, for sufficiently large odd primes the literal congruence
homology vanishes simultaneously in the finite rank window required by d. -/
theorem uniform_gamma_vanishing (N : ℕ) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Odd p → Q < p →
      ∀ j : ℕ, 0 < j → ∀ a : ℕ, 2*j+2 ≤ a → a ≤ N →
        ∀ m : ℕ, 1 ≤ m →
          IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  obtain ⟨Q,hQ⟩ := uniform_u_homology N
  exact ⟨Q,fun p _ hp hQp => gamma_vanishing_of_u p N hp (hQ p hp hQp)⟩

/-- Zero target homology makes every actual stabilization cokernel zero,
including its literal transition map. -/
theorem proZero_of_target_vanishing (p a j : ℕ)
    (hz : ∀ m : ℕ, 1 ≤ m →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a+1) m) (ZMod 2)) j)) :
    CongruenceCokernels.ProZero p a j := by
  intro m hm
  have : Subsingleton (CongruenceCokernels.H p (a+1) m j) :=
    ModuleCat.subsingleton_of_isZero (hz m hm)
  have hs : Function.Surjective (CongruenceCokernels.stabilization p a m j) :=
    fun x => ⟨0,Subsingleton.elim _ _⟩
  have : Subsingleton (CongruenceCokernels.C p a m j) :=
    (Cokernel.surjective_iff_coker_subsingleton _).mp hs
  exact ⟨m,le_refl m,Subsingleton.elim _ _⟩

/-- The manuscript's full theorem, with one positive weighted coboundary
expansion constant in ALL degrees below d and all members of the family. -/
theorem main : MainStatement := by
  apply reduction_to_positive_open_inputs
  intro d hd
  obtain ⟨Q₁,hQ₁⟩ := uniform_infinite_coset_positive (2*d) (by omega)
  obtain ⟨Q₂,hQ₂⟩ := actual_uniform_cosystolic (2*d) (by omega)
  obtain ⟨Q₃,hQ₃⟩ := uniform_gamma_vanishing (2*d+1)
  obtain ⟨p,hbound,hp⟩ := Nat.exists_infinite_primes (max 3 (max Q₁ (max Q₂ Q₃))+1)
  have hQ : max 3 (max Q₁ (max Q₂ Q₃)) < p := by omega
  have hp2 : p ≠ 2 := by have := le_max_left 3 (max Q₁ (max Q₂ Q₃)); omega
  have ho : Odd p := hp.odd_of_ne_two hp2
  let : Fact p.Prime := ⟨hp⟩
  have h₁ : Q₁ < p := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hQ
  have h₂ : Q₂ < p := lt_of_le_of_lt
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hQ
  have h₃ : Q₃ < p := lt_of_le_of_lt
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hQ
  refine ⟨p,hp,ho,hQ₁ p h₁,?_,hQ₂ p inferInstance h₂⟩
  intro j hj hjd
  constructor
  · apply proZero_of_target_vanishing
    intro m hm
    exact hQ₃ p ho h₃ j hj (2*d-1+1) (by omega) (by omega) m hm
  · apply proZero_of_target_vanishing
    intro m hm
    exact hQ₃ p ho h₃ j hj (2*d+1) (by omega) (by omega) m hm

end CoboundaryExpanders

end

end OAI
