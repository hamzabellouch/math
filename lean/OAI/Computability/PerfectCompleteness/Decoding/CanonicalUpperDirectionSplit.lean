import OAI.Computability.PerfectCompleteness.Foundations.CanonicalDirections
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas

namespace OAI

section

namespace PerfectCompleteness.CanonicalUpperDirectionSplit

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

variable {n : Nat}

abbrev Complement (rows : Nat → Nat) (upper : Fin n) :=
  FiniteProductSplit.Others
    (Ω := fun level : Fin n => PrefixTests.LevelDirection rows level) upper

def splitEquiv (rows : Nat → Nat) (upper : Fin n) :
    CanonicalDirections.Tuple rows n ≃
      PrefixTests.LevelDirection rows upper × Complement rows upper :=
  Equiv.piSplitAt upper (fun level => PrefixTests.LevelDirection rows level)

def complement (rows : Nat → Nat) (upper : Fin n)
    (directions : CanonicalDirections.Tuple rows n) : Complement rows upper :=
  (splitEquiv rows upper directions).2

def assemble (rows : Nat → Nat) (upper : Fin n)
    (direction : PrefixTests.LevelDirection rows upper) (rest : Complement rows upper) :
    CanonicalDirections.Tuple rows n :=
  (splitEquiv rows upper).symm (direction, rest)

@[simp] theorem split_selected (rows : Nat → Nat) (upper : Fin n)
    (directions : CanonicalDirections.Tuple rows n) :
    (splitEquiv rows upper directions).1 = directions upper := rfl

@[simp] theorem complement_apply (rows : Nat → Nat) (upper : Fin n)
    (directions : CanonicalDirections.Tuple rows n) (i : {i : Fin n // i ≠ upper}) :
    complement rows upper directions i = directions i.val := rfl

@[simp] theorem assemble_at_upper (rows : Nat → Nat) (upper : Fin n)
    (direction : PrefixTests.LevelDirection rows upper) (rest : Complement rows upper) :
    assemble rows upper direction rest upper = direction := by
  exact congrArg Prod.fst ((splitEquiv rows upper).apply_symm_apply (direction, rest))

@[simp] theorem assemble_at_other (rows : Nat → Nat) (upper : Fin n)
    (direction : PrefixTests.LevelDirection rows upper) (rest : Complement rows upper)
    (i : Fin n) (hne : i ≠ upper) :
    assemble rows upper direction rest i = rest ⟨i, hne⟩ := by
  exact congrArg
    (fun z : PrefixTests.LevelDirection rows upper × Complement rows upper => z.2 ⟨i, hne⟩)
    ((splitEquiv rows upper).apply_symm_apply (direction, rest))

theorem assemble_split (rows : Nat → Nat) (upper : Fin n)
    (directions : CanonicalDirections.Tuple rows n) :
    assemble rows upper (directions upper) (complement rows upper directions) = directions :=
  (splitEquiv rows upper).symm_apply_apply directions

theorem lower_preserved (rows : Nat → Nat) (upper lower : Fin n) (hne : lower ≠ upper)
    (direction : PrefixTests.LevelDirection rows upper)
    (directions : CanonicalDirections.Tuple rows n) :
    assemble rows upper direction (complement rows upper directions) lower = directions lower := by
  rw [assemble_at_other rows upper direction (complement rows upper directions) lower hne]
  rfl

def complementLaw (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) (upper : Fin n) :
    FiniteDistribution (Complement rows upper) :=
  FiniteProductSplit.otherLaw (CanonicalDirections.levelLaw rows hrows) upper

theorem split_law (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) (upper : Fin n) :
    (CanonicalDirections.law rows n hrows).pushforward (splitEquiv rows upper) =
      (CanonicalDirections.levelLaw rows hrows upper).product (complementLaw rows hrows upper) :=
  FiniteProductSplit.split_law (CanonicalDirections.levelLaw rows hrows) upper

theorem assemble_law (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) (upper : Fin n) :
    ((CanonicalDirections.levelLaw rows hrows upper).product
      (complementLaw rows hrows upper)).pushforward
        (fun z => assemble rows upper z.1 z.2) = CanonicalDirections.law rows n hrows := by
  have h := congrArg
    (fun μ : FiniteDistribution (PrefixTests.LevelDirection rows upper × Complement rows upper) =>
      μ.pushforward (splitEquiv rows upper).symm) (split_law rows hrows upper)
  rw [FiniteDistribution.pushforward_comp] at h
  have hid : (fun directions : CanonicalDirections.Tuple rows n =>
      (splitEquiv rows upper).symm (splitEquiv rows upper directions)) = id := by
    funext directions
    exact (splitEquiv rows upper).symm_apply_apply directions
  rw [hid, FiniteDistribution.pushforward_id] at h
  exact h.symm

theorem selected_law (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1)) (upper : Fin n) :
    (CanonicalDirections.law rows n hrows).pushforward (fun directions => directions upper) =
      CanonicalDirections.levelLaw rows hrows upper :=
  FiniteProduct.eval_pushforward (CanonicalDirections.levelLaw rows hrows) upper

theorem probability_split (rows : Nat → Nat) (hrows : ∀ k, 0 < rows (k + 1))
    (upper : Fin n) (event : CanonicalDirections.Tuple rows n → Bool) :
    (CanonicalDirections.law rows n hrows).probability event =
      ((CanonicalDirections.levelLaw rows hrows upper).product
        (complementLaw rows hrows upper)).probability
          (fun z => event (assemble rows upper z.1 z.2)) := by
  rw [← assemble_law rows hrows upper, FiniteDistribution.probability_pushforward]

theorem probability_complement_first (rows : Nat → Nat)
    (hrows : ∀ k, 0 < rows (k + 1)) (upper : Fin n)
    (event : CanonicalDirections.Tuple rows n → Bool) :
    (CanonicalDirections.law rows n hrows).probability event =
      (complementLaw rows hrows upper).expectation (fun rest =>
        (CanonicalDirections.levelLaw rows hrows upper).probability
          (fun direction => event (assemble rows upper direction rest))) := by
  rw [probability_split rows hrows upper]
  exact UsefulAdvice.product_probability_advice_first _ _ _

theorem lower_choice_preserved {branch : Nat → Nat} (rows : Nat → Nat)
    (leaf : RecursiveSpaces.Slots branch n) (upper lower : Fin n) (hne : lower ≠ upper)
    (direction : PrefixTests.LevelDirection rows upper)
    (directions : CanonicalDirections.Tuple rows n) :
    PrefixTests.choiceAt rows leaf lower
        (assemble rows upper direction (complement rows upper directions) lower) =
      PrefixTests.choiceAt rows leaf lower (directions lower) := by
  rw [lower_preserved rows upper lower hne direction directions]

end
end PerfectCompleteness.CanonicalUpperDirectionSplit

end

end OAI
