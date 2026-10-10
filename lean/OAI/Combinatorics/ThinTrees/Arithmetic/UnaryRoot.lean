import Mathlib
import OAI.Combinatorics.ThinTrees.Normalization.Realization

namespace OAI

/-! Unary root. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

abbrev rootCode := prodCode natCode natCode

def unaryRootStep (d : ℕ) (a : ℕ×ℕ) : ℕ×ℕ :=
  (a.1,if (a.2+1)^d ≤ a.1 then a.2+1 else a.2)

def unaryRootStepProgram (d : ℕ) : Realizes rootCode rootCode (unaryRootStep d) :=
  let r := first natCode natCode
  let b := second natCode natCode
  let next := b.then natSucc
  (r.both (((next.then (AlgorithmicThinTrees.Normalization.Stack.unaryPow d)).both r).then natLE |>.ite next b)).congr (by
    intro a; simp [unaryRootStep])
instance poly_unaryRootStep (d : ℕ) : PolyTime (unaryRootStepProgram d) := by
  unfold unaryRootStepProgram
  apply poly_congr

lemma unaryRootStep_iterate_bound (d k : ℕ) (a : ℕ×ℕ) :
    ((unaryRootStep d)^[k] a).1=a.1 ∧ ((unaryRootStep d)^[k] a).2≤a.2+k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [unaryRootStep]
    constructor
    · exact ih.1
    · split <;> omega

instance size_unaryRootStep (d : ℕ) : IterateSize (unaryRootStepProgram d) := by
  refine ⟨⟨X,?_⟩⟩
  intro a k
  have h := unaryRootStep_iterate_bound d k a
  change (rootCode ((unaryRootStep d)^[k] a)).length≤(rootCode a).length+k
  simp only [rootCode,prodCode_length,natCode,List.length_replicate,h.1]
  omega

lemma unaryRootStep_iterate_zero (d : ℕ) (hd : d≠0) (r k : ℕ) :
    ((unaryRootStep d)^[k] (r,0)).2=min k (Nat.nthRoot d r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [unaryRootStep]
    simp only [(unaryRootStep_iterate_bound d k (r,0)).1,ih]
    simp only [←Nat.le_nthRoot_iff hd]
    split <;> omega

lemma unaryRoot_le (d r : ℕ) (hd : d≠0) : Nat.nthRoot d r≤r :=
  (Nat.le_self_pow hd _).trans (Nat.pow_nthRoot_le (Or.inl hd))

def unaryRoot (d : ℕ) (hd : d≠0) : Realizes natCode natCode (Nat.nthRoot d) :=
  (((identity natCode).both ((identity natCode).both (constant natCode natCode 0))).then
    (unaryRootStepProgram d).iterate |>.then (second natCode natCode)).congr (by
      intro r
      change ((unaryRootStep d)^[r] (r,0)).2 = Nat.nthRoot d r
      rw [unaryRootStep_iterate_zero d hd r r,min_eq_right (unaryRoot_le d r hd)])
instance poly_unaryRoot (d : ℕ) (hd : d≠0) : PolyTime (unaryRoot d hd) := by
  unfold unaryRoot;infer_instance
end CurrentKS.Realization
end

end OAI
