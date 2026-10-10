import OAI.Combinatorics.ContingencyTables.Transport.IntegerRecursiveFlow

namespace OAI

/-! # The literal sum of future-slot correction kernels

Each summand gives exactly one unexposed ordinary pair occupancy M+1,
with multiplier a(M+1-a); every other pair is summed at its ordinary
balance. The coordinate changes below preserve complete configurations.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open BalancedFamily BalancedEnumeration IntegerMarginal

universe u

def exposePullback {I : Type u} (Ms : List ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) :
    (Coordinates (I ⊕ Bool) Ms → ℕ) → ℝ :=
  fun x => F (x ∘ (exposeEquiv (I := I) Ms).symm)

lemma exposed_profile {I : Type u} (Ms : List ℕ)
    (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (a b : ℕ) :
    exposedFamily Ms F (profile z a b) =
      eliminate Ms (fun x => F (profile x a b)) z := by
  unfold exposedFamily
  simp only [eliminate_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [expose_embedding]

lemma expose_pair {I : Type u} (Ms : List ℕ) (V : ℕ)
    (x : Coordinates (I ⊕ Bool) Ms → ℕ) (a b : ℕ) :
    (profile x a b) ∘ (exposeEquiv (I := I) (V::Ms)).symm =
      (profile (x ∘ (exposeEquiv (I := I) Ms).symm) a b) ∘ swapPairs := by
  funext t
  rcases t with (i | c) | c <;> rfl

lemma exposed_double_profile {I : Type u} (Ms : List ℕ) (V : ℕ)
    (F : (((Coordinates I Ms ⊕ Bool) ⊕ Bool) → ℕ) → ℝ)
    (z : I → ℕ) (j k a b : ℕ) :
    exposedFamily Ms (exposePullback (V::Ms) F) (profile (profile z j k) a b) =
      eliminate Ms (fun x => F (profile (profile x a b) j k)) z := by
  unfold exposedFamily exposePullback
  simp only [eliminate_eq_sum]
  apply Finset.sum_congr rfl
  intro v _
  change F ((embedding Ms (profile (profile z j k) a b) v ∘
    (exposeEquiv (I := I ⊕ Bool) Ms).symm) ∘
    (exposeEquiv (I := I) (V::Ms)).symm) = _
  have he := expose_embedding Ms (profile z j k) a b v
  change embedding Ms (profile (profile z j k) a b) v ∘
    (exposeEquiv (I := I ⊕ Bool) Ms).symm = _ at he
  rw [he, expose_pair]
  have he' := expose_embedding Ms z j k v
  change embedding Ms (profile z j k) v ∘ (exposeEquiv (I := I) Ms).symm = _ at he'
  rw [he']
  exact congrArg F (profile_swap (embedding Ms z v) a b j k)

lemma eliminate_sum {I : Type u} {A : Type*} (Ms : List ℕ) (s : Finset A)
    (F : A → (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    eliminate Ms (fun x => ∑ a ∈ s, F a x) z =
      ∑ a ∈ s, eliminate Ms (F a) z := by
  simp only [eliminate_eq_sum]
  rw [Finset.sum_comm]

lemma eliminate_mul {I : Type u} (Ms : List ℕ) (r : ℝ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (z : I → ℕ) :
    eliminate Ms (fun x => r*F x) z = r*eliminate Ms F z := by
  simp only [eliminate_eq_sum, Finset.mul_sum]

/-- The same current and future profiles occur on both sides, including
the complete fixed-domain sum over every other ordinary slot. -/
lemma weighted_exposed_commute {I : Type u} (Ms : List ℕ) (U V : ℕ)
    (F : (((Coordinates I Ms ⊕ Bool) ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) :
    weightedFuture (exposedFamily Ms (marginal F U)) (V+1) z =
      marginal (weightedFuture (exposedFamily Ms (exposePullback (V::Ms) F)) (V+1)) U z := by
  unfold weightedFuture
  conv_lhs => tactic => simp_rw [exposed_profile, marginal, eliminate_sum, Finset.mul_sum]
  unfold marginal
  rw [Finset.sum_comm]
  simp_rw [exposed_double_profile]

lemma pullback_marginal {I : Type u} (Ms : List ℕ) (V : ℕ)
    (F : (((Coordinates I Ms ⊕ Bool) ⊕ Bool) → ℕ) → ℝ) :
    marginal (exposePullback (V::Ms) F) V =
      exposePullback Ms (marginal (fun x => F (x ∘ swapPairs)) V) := by
  funext x
  unfold marginal exposePullback
  apply Finset.sum_congr rfl
  intro j _
  rw [expose_pair]

lemma marginal_swap_commute {J : Type u} (F : (((J ⊕ Bool) ⊕ Bool) → ℕ) → ℝ)
    (U V : ℕ) :
    marginal (marginal F U) V = marginal (marginal (fun x => F (x ∘ swapPairs)) V) U := by
  funext z
  unfold marginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg F (profile_swap z a (V-a) j (U-j)).symm

noncomputable def correctionKernel {I : Type u} : (Ms : List ℕ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → ℝ
  | [], _ => fun _ => 0
  | U::Ms, F => fun z => weightedFuture (exposedFamily Ms F) (U+1) z +
      correctionKernel Ms (marginal F U) z

theorem correctionKernel_nonnegative {I : Type u} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    0 ≤ correctionKernel Ms F z := by
  induction Ms with
  | nil => exact le_rfl
  | cons U Ms ih =>
    apply add_nonneg
    · apply weightedFuture_nonnegative
      intro x
      exact eliminate_nonnegative Ms _ (fun p => hF _) x
    · apply ih
      intro x
      exact Finset.sum_nonneg (fun j _ => hF _)

/-- Summing the currently exposed pair commutes with the literal sum
of all the other future corrections. -/
theorem correctionKernel_current_commute : ∀ (Ms : List ℕ) {I : Type u}
    (U : ℕ) (F : ((Coordinates I Ms ⊕ Bool) → ℕ) → ℝ),
    correctionKernel Ms (marginal F U) =
      marginal (correctionKernel Ms (exposePullback Ms F)) U := by
  intro Ms
  induction Ms with
  | nil => intro I U F; funext z; simp [correctionKernel, marginal]
  | cons V Ms ih =>
    intro I U F
    funext z
    change weightedFuture (exposedFamily Ms (marginal F U)) (V+1) z +
      correctionKernel Ms (marginal (marginal F U) V) z =
      ∑ j ∈ Finset.range (U+1),
        (weightedFuture (exposedFamily Ms (exposePullback (V::Ms) F)) (V+1)
          (profile z j (U-j)) +
        correctionKernel Ms (marginal (exposePullback (V::Ms) F) V) (profile z j (U-j)))
    rw [Finset.sum_add_distrib, weighted_exposed_commute, marginal_swap_commute]
    have ht := congrFun (ih U (marginal (fun x => F (x ∘ swapPairs)) V)) z
    rw [← pullback_marginal] at ht
    rw [ht]
    rfl

end ContingencyTables.IntegerWeightedTransport

end OAI
