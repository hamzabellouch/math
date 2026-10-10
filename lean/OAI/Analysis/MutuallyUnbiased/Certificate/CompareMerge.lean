import OAI.Analysis.MutuallyUnbiased.Certificate.IntegerMerge

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

def mergeByFuel (less : ι → ι → Bool) : ℕ → Sparse ι → Sparse ι → Sparse ι
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | fuel + 1, a :: as, b :: bs =>
      if less a.1 b.1 then a :: mergeByFuel less fuel as (b :: bs)
      else if a.1 = b.1 then
        if a.2 + b.2 = 0 then mergeByFuel less fuel as bs
        else (a.1, a.2 + b.2) :: mergeByFuel less fuel as bs
      else b :: mergeByFuel less fuel (a :: as) bs

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

def mergeBy (less : ι → ι → Bool) (a b : Sparse ι) : Sparse ι :=
  mergeByFuel less (a.length + b.length) a b

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

def collect (less : ι → ι → Bool) (v : Sparse ι) : Sparse ι :=
  v.foldr (fun p acc => mergeBy less [p] acc) []

@[simp] theorem eval_collect (less : ι → ι → Bool) (v : Sparse ι) (x : ι → ℝ) :
    eval (collect less v) x = eval v x := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    change eval (mergeBy less [p] (collect less v)) x = _
    rw [eval_mergeBy, ih]
    simp

omit [DecidableEq ι] in
theorem eval_flatten (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval vs.flatten x = (vs.map (fun v => eval v x)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

def mergePairs (less : ι → ι → Bool) : List (Sparse ι) → List (Sparse ι)
  | [] => []
  | [a] => [a]
  | a :: b :: rest => mergeBy less a b :: mergePairs less rest

theorem eval_mergePairs (less : ι → ι → Bool) (vs : List (Sparse ι)) (x : ι → ℝ) :
    ((mergePairs less vs).map (fun v => eval v x)).sum =
      (vs.map (fun v => eval v x)).sum := by
  induction vs using mergePairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih => simp [mergePairs, ih, add_assoc]

def collectLevels (less : ι → ι → Bool) : ℕ → List (Sparse ι) → Sparse ι
  | 0, vs => vs.flatten
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | fuel + 1, a :: b :: rest => collectLevels less fuel (mergePairs less (a :: b :: rest))

theorem eval_collectLevels (less : ι → ι → Bool) (fuel : ℕ)
    (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval (collectLevels less fuel vs) x = (vs.map (fun v => eval v x)).sum := by
  induction fuel generalizing vs with
  | zero => exact eval_flatten vs x
  | succ fuel ih =>
    cases vs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => simp [collectLevels]
      | cons b rest =>
        rw [collectLevels, ih, eval_mergePairs]

def collectBalanced (less : ι → ι → Bool) (v : Sparse ι) : Sparse ι :=
  collectLevels less v.length (v.map fun p => [p])

@[simp] theorem eval_collectBalanced (less : ι → ι → Bool) (v : Sparse ι) (x : ι → ℝ) :
    eval (collectBalanced less v) x = eval v x := by
  rw [collectBalanced, eval_collectLevels]
  simp [eval, Function.comp_def]

end MUB6.Certificate.Integer.Sparse

end OAI
