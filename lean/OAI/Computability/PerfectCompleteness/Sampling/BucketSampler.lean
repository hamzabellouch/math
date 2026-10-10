import Mathlib.Algebra.Field.ZMod
import OAI.Computability.PerfectCompleteness.Algebra.EvaluationMatrix
import OAI.Computability.PerfectCompleteness.Sampling.RecordSeedSamplingLemmas

namespace OAI


namespace PerfectCompleteness.BucketSampler

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

abbrev F2 := ZMod 2

abbrev Direction (ℓ : Nat) := {v : Fin ℓ → F2 // v ≠ 0}

abbrev Tape (ℓ : Nat) (Ω : Type*) := Direction ℓ → Ω

variable {Ω H : Type*} [AddCommGroup H] [Module F2 H]

def rankOne {ℓ : Nat} (v : Fin ℓ → F2) (h : H) : Fin ℓ → H :=
  fun i => v i • h

def evaluate (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω) : Fin ℓ → H :=
  fun i => ∑ v : Direction ℓ, v.val i • eval (t v)

theorem evaluate_eq_sum (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω) :
    evaluate ℓ eval t = ∑ v : Direction ℓ, rankOne v.val (eval (t v)) := by
  funext i
  simp only [evaluate, Finset.sum_apply, rankOne]

theorem evaluate_update (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω)
    (a : Direction ℓ) (new : Ω) :
    evaluate ℓ eval (Function.update t a new) =
      evaluate ℓ eval t + rankOne a.val (eval new - eval (t a)) := by
  funext i
  let S : H := ∑ v : Direction ℓ, v.val i • eval (t v)
  let S' : H := ∑ v : Direction ℓ, v.val i • eval (Function.update t a new v)
  have hd : S' - S = a.val i • (eval new - eval (t a)) := by
    dsimp only [S', S]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
    · rw [Function.update_self, smul_sub]
    · intro b _ hba
      simp only [Function.update_of_ne hba, sub_self]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  change S' = S + a.val i • (eval new - eval (t a))
  simpa only [sub_add_cancel] using
    (congrArg (fun z : H => z + S) hd).trans (add_comm _ _)

theorem linearMap_evaluate (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω)
    (q : H →ₗ[F2] F2) (i : Fin ℓ) :
    q (evaluate ℓ eval t i) = ∑ v : Direction ℓ, v.val i * q (eval (t v)) := by
  simp only [evaluate, map_sum, map_smul, smul_eq_mul]

theorem evaluate_apply {X : Type*} (ℓ : Nat) (V : Submodule F2 (X → F2))
    (eval : Ω → V) (t : Tape ℓ Ω) (i : Fin ℓ) (x : X) :
    (evaluate ℓ eval t i).val x =
      ∑ v : Direction ℓ, v.val i * (eval (t v)).val x :=
  linearMap_evaluate ℓ eval t (EvaluationMatrix.evaluation V x) i

instance directionZero_isEmpty : IsEmpty (Direction 0) where
  false v := v.property (funext fun i => Fin.elim0 i)

@[simp] theorem evaluate_zero_width (eval : Ω → H) (t : Tape 0 Ω) :
    evaluate 0 eval t = 0 := by
  funext i
  exact Fin.elim0 i

section Laws

variable [Fintype Ω]

def tapeLaw (ℓ : Nat) (μ : FiniteDistribution Ω) : FiniteDistribution (Tape ℓ Ω) :=
  FiniteProduct.law (fun _ : Direction ℓ => μ)

@[simp] theorem tapeLaw_weight (ℓ : Nat) (μ : FiniteDistribution Ω) (t : Tape ℓ Ω) :
    (tapeLaw ℓ μ).weight t = ∏ v : Direction ℓ, μ.weight (t v) := rfl

theorem tapeLaw_marginal (ℓ : Nat) (μ : FiniteDistribution Ω) (v : Direction ℓ) :
    (tapeLaw ℓ μ).pushforward (fun t => t v) = μ :=
  FiniteProduct.eval_pushforward (fun _ : Direction ℓ => μ) v

theorem expectation_product (ℓ : Nat) (μ : FiniteDistribution Ω)
    (f : Direction ℓ → Ω → ℝ) :
    (tapeLaw ℓ μ).expectation (fun t => ∏ v, f v (t v)) =
      ∏ v, μ.expectation (f v) :=
  FiniteProduct.expectation_product (fun _ : Direction ℓ => μ) f

omit [AddCommGroup H] [Module F2 H] in
theorem expectation_bucket_mul (ℓ : Nat) (μ : FiniteDistribution Ω)
    (eval : Ω → H) (v w : Direction ℓ) (hvw : v ≠ w) (f g : H → ℝ) :
    (tapeLaw ℓ μ).expectation (fun t => f (eval (t v)) * g (eval (t w))) =
      μ.expectation (fun t => f (eval t)) * μ.expectation (fun t => g (eval t)) :=
  FiniteProduct.expectation_eval_mul (fun _ : Direction ℓ => μ) v w hvw
    (fun t => f (eval t)) (fun t => g (eval t))

@[simp] theorem tapeLaw_zero_width_weight (μ : FiniteDistribution Ω) (t : Tape 0 Ω) :
    (tapeLaw 0 μ).weight t = 1 := by
  simp [tapeLaw, FiniteProduct.law]

variable [Fintype H]

omit [AddCommGroup H] [Module F2 H] in
theorem bucket_marginal (ℓ : Nat) (μ : FiniteDistribution Ω) (eval : Ω → H)
    (v : Direction ℓ) :
    (tapeLaw ℓ μ).pushforward (fun t => eval (t v)) = μ.pushforward eval := by
  apply FiniteDistribution.eq_of_weight_eq
  intro h
  calc
    _ = (tapeLaw ℓ μ).expectation (fun t => if eval (t v) = h then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = μ.expectation (fun t => if eval t = h then 1 else 0) :=
      FiniteProduct.expectation_eval (fun _ : Direction ℓ => μ) v
        (fun t : Ω => if eval t = h then (1 : ℝ) else 0)
    _ = _ := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]

def law (ℓ : Nat) (μ : FiniteDistribution Ω) (eval : Ω → H) :
    FiniteDistribution (Fin ℓ → H) :=
  (tapeLaw ℓ μ).pushforward (evaluate ℓ eval)

theorem probability_law (ℓ : Nat) (μ : FiniteDistribution Ω) (eval : Ω → H)
    (event : (Fin ℓ → H) → Bool) :
    (law ℓ μ eval).probability event =
      (tapeLaw ℓ μ).probability (fun t => event (evaluate ℓ eval t)) :=
  FiniteDistribution.probability_pushforward _ _ _

end Laws

section FreshArrays

variable {J : Type*} [Fintype J] [DecidableEq J] [Fintype Ω]

abbrev FreshTape (J : Type*) (ℓ : Nat) (Ω : Type*) := J → Tape ℓ Ω

def freshTapeLaw (J : Type*) [Fintype J] [DecidableEq J] (ℓ : Nat)
    (μ : FiniteDistribution Ω) : FiniteDistribution (FreshTape J ℓ Ω) :=
  FiniteProduct.law (fun _ : J => tapeLaw ℓ μ)

theorem freshTapeLaw_marginal (ℓ : Nat) (μ : FiniteDistribution Ω) (j : J) :
    (freshTapeLaw J ℓ μ).pushforward (fun t => t j) = tapeLaw ℓ μ :=
  FiniteProduct.eval_pushforward (fun _ : J => tapeLaw ℓ μ) j

theorem freshArrays_expectation_product (ℓ : Nat) (μ : FiniteDistribution Ω)
    (eval : Ω → H) (f : J → (Fin ℓ → H) → ℝ) :
    (freshTapeLaw J ℓ μ).expectation
        (fun t => ∏ j, f j (evaluate ℓ eval (t j))) =
      ∏ j, (tapeLaw ℓ μ).expectation (fun t => f j (evaluate ℓ eval t)) :=
  FiniteProduct.expectation_product (fun _ : J => tapeLaw ℓ μ)
    (fun j t => f j (evaluate ℓ eval t))

end FreshArrays


open PointwiseSpaces RecursiveSpaces DescendantSpaces

universe u
variable {branch : Nat → Nat} {n m : Nat}

abbrev RecursiveTape (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) :=
  Tape ℓ (RecursiveSampler.Tape F2 repeats p A)

def recursiveEvaluate (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) (t : RecursiveTape ℓ repeats p A) :
    Fin ℓ → space F2 branch n A :=
  evaluate ℓ (RecursiveSampler.evaluate F2 repeats p A) t

def recursiveTapeLaw (ℓ : Nat) (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] :
    FiniteDistribution (RecursiveTape ℓ repeats p A) :=
  tapeLaw ℓ (RecursiveSampler.tapeLaw F2 repeats p A)

theorem recursiveTapeLaw_marginal (ℓ : Nat) (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    (v : Direction ℓ) :
    (recursiveTapeLaw ℓ repeats p A).pushforward (fun t => t v) =
      RecursiveSampler.tapeLaw F2 repeats p A :=
  tapeLaw_marginal ℓ (RecursiveSampler.tapeLaw F2 repeats p A) v

theorem recursiveBucket_marginal (ℓ : Nat) (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u) [∀ s, Finite (A s)]
    [Fintype (space F2 branch n A)] (v : Direction ℓ) :
    (recursiveTapeLaw ℓ repeats p A).pushforward
        (fun t => RecursiveSampler.evaluate F2 repeats p A (t v)) =
      RecursiveSampler.law F2 repeats p A :=
  bucket_marginal ℓ (RecursiveSampler.tapeLaw F2 repeats p A)
    (RecursiveSampler.evaluate F2 repeats p A) v

theorem recursiveEvaluate_apply (ℓ : Nat) (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u)
    (t : RecursiveTape ℓ repeats p A) (i : Fin ℓ) (x : Assignment A) :
    (recursiveEvaluate ℓ repeats p A t i).val x =
      ∑ v : Direction ℓ, v.val i *
        (RecursiveSampler.evaluate F2 repeats p A (t v)).val x :=
  evaluate_apply ℓ (space F2 branch n A) (RecursiveSampler.evaluate F2 repeats p A) t i x

end
end PerfectCompleteness.BucketSampler

end OAI
