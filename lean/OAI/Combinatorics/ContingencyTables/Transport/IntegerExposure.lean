import OAI.Combinatorics.ContingencyTables.Transport.BalancedEnumeration
import OAI.Combinatorics.ContingencyTables.Transport.IntegerFutureKernel
import OAI.Combinatorics.ContingencyTables.Transport.IntegerSliceReindex

namespace OAI

/-! # Exposing an ordinary pair in the actual balanced marginal

Moving one pair into the retained coordinates changes only the coordinate
bijection. The remaining finite assignment sum is the same, so the actual
balanced marginal partitions into precisely the U+1 child families.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

/-- Move the outermost pair inside all the other still-summed pairs. -/
def exposeEquiv {I : Type u} : (Ms : List ℕ) →
    Coordinates (I ⊕ Bool) Ms ≃ Coordinates I Ms ⊕ Bool
  | [] => Equiv.refl _
  | _::Ms => (Equiv.sumCongr (exposeEquiv (I := I) Ms) (Equiv.refl Bool)).trans swapPairs

lemma expose_embedding {I : Type*} (Ms : List ℕ) (z : I → ℕ) (a b : ℕ)
    (u : Assignments Ms) :
    (fun t => embedding Ms (profile z a b) u ((exposeEquiv (I := I) Ms).symm t)) =
      profile (embedding Ms z u) a b := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    funext t
    rcases t with (i | c) | c
    · change embedding Ms (profile z a b) u.1 ((exposeEquiv (I := I) Ms).symm (.inl i)) =
        embedding Ms z u.1 i
      exact congrFun (ih u.1) (.inl i)
    · cases c <;> rfl
    · change embedding Ms (profile z a b) u.1 ((exposeEquiv (I := I) Ms).symm (.inr c)) = _
      exact congrFun (ih u.1) (.inr c)

noncomputable def exposedFamily {I : Type*} (Ms : List ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) : ((I ⊕ Bool) → ℕ) → ℝ :=
  eliminate Ms (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))

/-- The literal child family sums back to its actual parent; the domain
is the same Cartesian product of all remaining balanced profiles. -/
theorem exposed_marginal {I : Type*} (Ms : List ℕ) (U : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) :
    marginal (exposedFamily Ms F) U = eliminate (U::Ms) F := by
  funext z
  change (∑ j ∈ Finset.range (U+1), exposedFamily Ms F (profile z j (U-j))) =
    eliminate Ms (marginal F U) z
  simp only [exposedFamily, eliminate_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  unfold marginal
  apply Finset.sum_congr rfl
  intro j _
  rw [expose_embedding]


lemma expose_bounds {I : Type*} (Ms : List ℕ) (m : I → ℕ) (U : ℕ) :
    (fun t => bounds (profile m U U) Ms ((exposeEquiv (I := I) Ms).symm t)) =
      profile (bounds m Ms) U U := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
    funext t
    rcases t with (i | c) | c
    · change bounds (profile m U U) Ms ((exposeEquiv (I := I) Ms).symm (.inl i)) = bounds m Ms i
      exact congrFun ih (.inl i)
    · cases c <;> rfl
    · change bounds (profile m U U) Ms ((exposeEquiv (I := I) Ms).symm (.inr c)) = _
      exact congrFun ih (.inr c)


lemma expose_bounds_forward {I : Type*} (Ms : List ℕ) (m : I → ℕ) (U : ℕ) :
    (profile (bounds m Ms) U U) ∘ exposeEquiv (I := I) Ms = bounds (profile m U U) Ms := by
  funext t
  have he := congrFun (expose_bounds Ms m U) (exposeEquiv (I := I) Ms t)
  simpa only [Equiv.symm_apply_apply, Function.comp_apply] using he.symm

/-- Remaining balanced marginalization supplies the exposed child
family's positivity and signature on the exact required total slice. -/
theorem exposed_slices {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (U : ℕ) (m : I → ℕ) (R : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ)
    (hwidth : ∀ M ∈ Ms, 2 ≤ M)
    (hpos : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum)) :
    BalancedBox.PositiveSlice (exposedFamily Ms F) (profile m U U) (R+U) ∧
      BalancedBox.RemovalSlice (exposedFamily Ms F) (profile m U U) (R+U) := by
  apply eliminate_slices Ms (profile m U U) (R+U) _ hwidth
  · have hp := positiveSlice_reindex (exposeEquiv (I := I) Ms) F (profile (bounds m Ms) U U)
      (R+U+Ms.sum) hpos
    rw [expose_bounds_forward] at hp
    exact hp
  · have hs := removalSlice_reindex (exposeEquiv (I := I) Ms) F (profile (bounds m Ms) U U)
      (R+U+Ms.sum) hsig
    rw [expose_bounds_forward] at hs
    exact hs


theorem expose_source_positive {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (U : ℕ) (m : I → ℕ) (R : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ)
    (hpos : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum)) :
    BalancedBox.PositiveSlice (fun x => F (fun t => x ((exposeEquiv (I := I) Ms).symm t)))
      (bounds (profile m U U) Ms) (R+U+Ms.sum) := by
  have hp := positiveSlice_reindex (exposeEquiv (I := I) Ms) F (profile (bounds m Ms) U U)
    (R+U+Ms.sum) hpos
  rw [expose_bounds_forward] at hp
  exact hp

theorem eliminate_positive {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (m : I → ℕ) (R : ℕ) (F : (Coordinates I Ms → ℕ) → ℝ)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R+Ms.sum)) :
    BalancedBox.PositiveSlice (eliminate Ms F) m R := by
  induction Ms with
  | nil => simpa only [List.sum_nil, add_zero, eliminate, bounds] using hpos
  | cons U Ms ih =>
    apply ih (marginal F U)
    apply BalancedBox.marginal_positive_slice F (bounds m Ms) (R+Ms.sum) U
    rw [show R+Ms.sum+U=R+(U::Ms).sum by simp only [List.sum_cons]; omega]
    exact hpos

theorem exposed_positive {I : Type*} [Fintype I] [DecidableEq I]
    (Ms : List ℕ) (U : ℕ) (m : I → ℕ) (R : ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ)
    (hpos : BalancedBox.PositiveSlice F (profile (bounds m Ms) U U) (R+U+Ms.sum)) :
    BalancedBox.PositiveSlice (exposedFamily Ms F) (profile m U U) (R+U) :=
  eliminate_positive Ms (profile m U U) (R+U) _ (expose_source_positive Ms U m R F hpos)

end ContingencyTables.IntegerWeightedTransport

end OAI
