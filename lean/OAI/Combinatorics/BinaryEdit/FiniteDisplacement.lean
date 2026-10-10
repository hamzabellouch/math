import OAI.Combinatorics.BinaryEdit.FiniteFourierAssembly
import OAI.Combinatorics.BinaryEdit.FiniteFourier
import OAI.Combinatorics.BinaryEdit.ScalarCutsBool
import OAI.Combinatorics.BinaryEdit.CutAggregation

namespace OAI

/-!
# Finite-group displacement for arbitrary maps to ℓ₁

The finite-group displacement identity `lem:finite-fourier` holds for maps
from any finite abelian group into `TreeEdit.RealL1`, the full space of
absolutely summable real sequences. No injectivity or finite-support
assumption is needed.

The proof combines finite scalar cuts, summable-coordinate aggregation,
Parseval's identity and finite nonnegative summation.
-/

noncomputable section

open scoped BigOperators

namespace TreeEdit.BinaryLower

/-- Concrete finite-cut representation of any finite family of absolutely
summable real sequences. The two constant cuts have zero weight. The final
bound is the half ordered-pair form of the finite total-mass estimate. -/
theorem l1_bool_cut_representation {S : Type*} [Fintype S] [DecidableEq S]
    (F : S → RealL1) :
    ∃ a : (S → Bool) → ℝ, (∀ C, 0 ≤ a C) ∧
      (∀ x y, ‖F x - F y‖ = ∑ C, a C * BoolCuts.cutDistance C x y) ∧
      a (fun _ => false) = 0 ∧ a (fun _ => true) = 0 ∧
      (∑ C, a C) ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2 := by
  classical
  choose a ha hrep hfalse htrue using
    (fun n : ℕ => BoolCuts.scalar_cut_representation (fun x => F x n))
  have hcut : ∀ C : S → Bool, (∀ n, a n C = 0) ∨
      ∃ x y, |BoolCuts.bit (C x) - BoolCuts.bit (C y)| = 1 := by
    intro C
    by_cases hf : C = fun _ => false
    · subst C
      exact Or.inl hfalse
    by_cases ht : C = fun _ => true
    · subst C
      exact Or.inl htrue
    right
    have hx : ∃ x, C x = true := by
      by_contra h
      push Not at h
      apply hf
      funext x
      cases hc : C x with
      | false => rfl
      | true => exact False.elim (h x hc)
    have hy : ∃ y, C y = false := by
      by_contra h
      push Not at h
      apply ht
      funext y
      cases hc : C y with
      | false => exact False.elim (h y hc)
      | true => rfl
    obtain ⟨x, hx⟩ := hx
    obtain ⟨y, hy⟩ := hy
    exact ⟨x, y, by simp [hx, hy, BoolCuts.bit]⟩
  obtain ⟨A, hA, hsum, hARep, hmass⟩ :=
    CutAggregation.aggregate_with_mass_bound F
      (fun (C : S → Bool) (x : S) => BoolCuts.bit (C x)) a ha hcut hrep
  refine ⟨A, hA, hARep, ?_, ?_, hmass⟩
  · simp [hsum, hfalse]
  · simp [hsum, htrue]

/-- The finite-group displacement lemma, for the actual full ℓ₁ sequence
space. Uniform probability averaging is denoted by `𝔼`. -/
theorem finite_group_displacement {A : Type*} [AddCommGroup A] [Fintype A]
    (F : A → RealL1) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧
      ∀ z, (𝔼 x, ‖F (x + z) - F x‖) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * H χ := by
  classical
  obtain ⟨a, ha, hrep, -, -, -⟩ := l1_bool_cut_representation F
  apply finite_fourier_of_cut_expansions F a
    (fun C x => BoolCuts.bit (C x))
    (fun C χ => ‖FiniteFourier.coefficient (fun x =>
      (BoolCuts.bit (C x) : ℂ)) χ‖ ^ 2) ha
  · intro C χ
    exact sq_nonneg _
  · exact hrep
  · intro C z
    have hC : ∀ x, BoolCuts.bit (C x) = 0 ∨ BoolCuts.bit (C x) = 1 := by
      intro x
      cases C x <;> simp [BoolCuts.bit]
    simpa only [Fintype.expect_eq_sum_div_card] using
      FiniteFourier.indicator_displacement (fun x => BoolCuts.bit (C x)) hC z

end TreeEdit.BinaryLower

end

end OAI
