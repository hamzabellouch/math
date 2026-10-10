import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordLieProjection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.TypeTags.Basic

namespace OAI

/-! # Unique ordered products of powers of distinct letters -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {n : ℕ}

def wordLetterCount (a : I) (w : FreeMonoid I) : ℕ :=
  (FreeMonoid.lift (fun b => Multiplicative.ofAdd (if b = a then (1 : ℕ) else 0)) w).toAdd

def orderedPowerWord (f : Fin n → I) (k : Fin n → ℕ) : FreeMonoid I :=
  (List.ofFn (fun i => FreeMonoid.of (f i) ^ k i)).prod

theorem wordLetterCount_orderedPowerWord (f : Fin n → I) (hf : Function.Injective f)
    (k : Fin n → ℕ) (j : Fin n) : wordLetterCount (f j) (orderedPowerWord f k) = k j := by
  simp only [wordLetterCount, orderedPowerWord, map_list_prod, List.map_ofFn, Function.comp_def,
    List.prod_ofFn, toAdd_prod, map_pow, FreeMonoid.lift_eval_of,
    toAdd_pow, toAdd_ofAdd, hf.eq_iff]
  simp

theorem orderedPowerWord_injective (f : Fin n → I) (hf : Function.Injective f) :
    Function.Injective (orderedPowerWord f) := by
  intro k l h
  funext j
  have hc := congrArg (wordLetterCount (f j)) h
  simpa only [wordLetterCount_orderedPowerWord f hf] using hc

end PolycyclicRecognition

end

end OAI
