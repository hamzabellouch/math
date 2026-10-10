import OAI.Combinatorics.BalancedRyser.Local.AlignedPointExposure
import OAI.Combinatorics.BalancedRyser.Local.LocalDirectionAssignments

namespace OAI

namespace Balanced.Local.TokenExposure

open AlignedListProbability TupleAlignment PartialAlignment
noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def tupleDirections (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) : Fin 4 → Direction F :=
  fun j => e (Sum.inr (P.classOf i j))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tupleDirections_injective (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) :
    Function.Injective (tupleDirections P e i) := by
  intro j k h
  exact P.withinTuple i (Sum.inr.inj (e.injective h))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tupleDirections_adjacent (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) :
    ∀ j, tupleDirections P e i j ≠ tupleDirections P e i (j+1) :=
  adjacent_ne_of_injective ⟨tupleDirections P e i, fun _ => false⟩
    (tupleDirections_injective P e i)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem tupleDirections_ne_target (P : EqualityPattern b κ)
    (e : DirectionToken b κ ↪ Direction F) (i : Fin b) :
    ∀ j, tupleDirections P e i j ≠ e (Sum.inl i) := by
  intro j h
  have hbad := e.injective h
  cases hbad

def pointKernel (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (i : Fin b) (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (a : (DirectionToken b κ ↪ Direction F) → Fin 4 → Bool → F)
    (e : DirectionToken b κ ↪ Direction F) : PMF (Fin 4 → Point F) :=
  generatedPointLaw (tupleDirections P e i) (tupleDirections_adjacent P e i)
    (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i)
    (lineEval (e (Sum.inl i)) p) J hJ (a e)

theorem pointKernel_dependsOnExposed (P : EqualityPattern b κ)
    (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (K : Finset (DirectionToken b κ)) (htarget : Sum.inl i ∈ K)
    (hold : ∀ j ∈ J, Sum.inr (P.classOf i j) ∈ K)
    (a : (DirectionToken b κ ↪ Direction F) → Fin 4 → Bool → F)
    (ha : ∀ e f, (∀ t ∈ K, e t = f t) → ∀ j ∈ J, a e j = a f j) :
    InjectionExposure.DependsOnExposed K (pointKernel P bits p i J hJ a) := by
  intro e f hef
  have ht : e (Sum.inl i) = f (Sum.inl i) := hef _ htarget
  have hd : ∀ j ∈ J, tupleDirections P e i j = tupleDirections P f i j := by
    intro j hj
    exact hef _ (hold j hj)
  have hg : ∀ j, tupleDirections P f i j ≠ e (Sum.inl i) := by
    simpa only [ht] using tupleDirections_ne_target P f i
  have h := generatedPointLaw_agree_old
    (tupleDirections P e i) (tupleDirections P f i)
    (tupleDirections_adjacent P e i) (tupleDirections_adjacent P f i)
    (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i) hg
    (lineEval (e (Sum.inl i)) p) J hJ (a e) (a f) hd (ha e f hef)
  simpa only [pointKernel, ht] using h

theorem pointKernel_fixed_dependsOnExposed (P : EqualityPattern b κ)
    (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (K : Finset (DirectionToken b κ)) (htarget : Sum.inl i ∈ K)
    (hold : ∀ j ∈ J, Sum.inr (P.classOf i j) ∈ K)
    (a : Fin 4 → Bool → F) :
    InjectionExposure.DependsOnExposed K (pointKernel P bits p i J hJ (fun _ => a)) :=
  pointKernel_dependsOnExposed P bits p i J hJ K htarget hold (fun _ => a)
    (fun _ _ _ _ _ => rfl)

end
end Balanced.Local.TokenExposure

end OAI
