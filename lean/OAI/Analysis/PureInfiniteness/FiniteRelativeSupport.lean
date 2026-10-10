import OAI.Analysis.PureInfiniteness.UltrapowerCopiesExact
import OAI.Analysis.PureInfiniteness.RelativeSupportAction

namespace OAI

/-! Finite relative copies on an arbitrary positive family. Commutativity of
that family is unnecessary: its sum is a single positive support element. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A P M : Type*} [NonUnitalCStarAlgebra A]
  [Fintype P] [Fintype M] [DecidableEq M]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem finite_relative_support_copies (hP : MainGap.PropertyP A)
    (x : P → N) (hx : ∀ p, 0 ≤ x p) :
    ∃ r : M → N, (∀ i, ‖r i‖ ≤ 1) ∧
      ∀ i j p, (star (r i) * r j) * x p = if i = j then x p else 0 := by
  classical
  let g := ∑ p, x p
  have hg : 0 ≤ g := Finset.sum_nonneg (fun p _ => hx p)
  have hle (p : P) : x p ≤ g := Finset.single_le_sum (fun q _ => hx q) (Finset.mem_univ p)
  obtain ⟨r, hr, _, hrel⟩ := ultrapower_relative_copies (M := M) U hP
    (fun _ : Unit => g) (fun _ => hg) (fun _ _ => Commute.refl g)
  refine ⟨r, hr, ?_⟩
  intro i j p
  have h := hrel () i j
  by_cases hij : i = j
  · rw [ite_eq_left hij] at h ⊢
    exact mul_eq_self_of_positive_le (hx p) (hle p) _ h
  · rw [ite_eq_right hij] at h ⊢
    exact mul_eq_zero_of_positive_le (hx p) (hle p) _ h

end WeakPureInfiniteness

end

end OAI
