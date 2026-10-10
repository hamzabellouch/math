import OAI.NumberTheory.Ostmann.Characters.TreeLeafProducts

namespace OAI

/-! # Computing every current parent product from previously exposed splits -/

namespace Ostmann

/-- Pending subtrees are visited in preorder. Depth-zero branches require
no split coordinate, so they are never stored in the frontier. -/
def pendingSplitBranch {G : Type*} (n : ℕ) (P : G) (rest : List (ℕ × G)) : List (ℕ × G) :=
  match n with
  | 0 => rest
  | n + 1 => (n + 1, P) :: rest

def splitFrontierStep {G : Type*} [Div G] (frontier : List (ℕ × G)) (x : G) : List (ℕ × G) :=
  match frontier with
  | [] => []
  | (0, _) :: rest => rest
  | (n + 1, P) :: rest => pendingSplitBranch n x (pendingSplitBranch n (P / x) rest)

def currentSplitParent {G : Type*} [One G] (frontier : List (ℕ × G)) : G :=
  match frontier with
  | [] => 1
  | (_, P) :: _ => P

def splitPrefixParent {G : Type*} [Div G] [One G] (n : ℕ) (P : G) (past : List G) : G :=
  currentSplitParent (past.foldr (fun x frontier => splitFrontierStep frontier x)
    (pendingSplitBranch n P []))

def actualSplitValues {G : Type*} [CommMonoid G] : (n : ℕ) → TreeLeafTuple G n → List G
  | 0, _ => []
  | n + 1, x => treeLeafProduct n x.1 :: (actualSplitValues n x.1 ++ actualSplitValues n x.2)

def actualParentSplits {G : Type*} [CommMonoid G] : (n : ℕ) → TreeLeafTuple G n → List (G × G)
  | 0, _ => []
  | n + 1, x => (treeLeafProduct (n + 1) x, treeLeafProduct n x.1) ::
      (actualParentSplits n x.1 ++ actualParentSplits n x.2)

def splitFrontierTrace {G : Type*} [Div G] [One G] (frontier : List (ℕ × G)) : List G → List (G × G)
  | [] => []
  | x :: xs => (currentSplitParent frontier, x) ::
      splitFrontierTrace (splitFrontierStep frontier x) xs

theorem splitFrontierTrace_append {G : Type*} [Div G] [One G]
    (frontier : List (ℕ × G)) (xs ys : List G) :
    splitFrontierTrace frontier (xs ++ ys) = splitFrontierTrace frontier xs ++
      splitFrontierTrace (xs.foldl splitFrontierStep frontier) ys := by
  induction xs generalizing frontier with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, splitFrontierTrace, List.foldl_cons, ih]

theorem splitFrontier_after_actual {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (rest : List (ℕ × G)) :
    (actualSplitValues n x).foldl splitFrontierStep
      (pendingSplitBranch n (treeLeafProduct n x) rest) = rest := by
  induction n generalizing rest with
  | zero => rfl
  | succ n ih =>
    change (actualSplitValues n x.1 ++ actualSplitValues n x.2).foldl splitFrontierStep
      (pendingSplitBranch n (treeLeafProduct n x.1)
        (pendingSplitBranch n ((treeLeafProduct n x.1 * treeLeafProduct n x.2) /
          treeLeafProduct n x.1) rest)) = rest
    rw [mul_div_cancel_left, List.foldl_append, ih, ih]

theorem splitFrontierTrace_actual {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (rest : List (ℕ × G)) :
    splitFrontierTrace (pendingSplitBranch n (treeLeafProduct n x) rest)
      (actualSplitValues n x) = actualParentSplits n x := by
  induction n generalizing rest with
  | zero => rfl
  | succ n ih =>
    change (treeLeafProduct n x.1 * treeLeafProduct n x.2, treeLeafProduct n x.1) ::
      splitFrontierTrace (pendingSplitBranch n (treeLeafProduct n x.1)
        (pendingSplitBranch n ((treeLeafProduct n x.1 * treeLeafProduct n x.2) /
          treeLeafProduct n x.1) rest)) (actualSplitValues n x.1 ++ actualSplitValues n x.2) =
      (treeLeafProduct n x.1 * treeLeafProduct n x.2, treeLeafProduct n x.1) ::
        (actualParentSplits n x.1 ++ actualParentSplits n x.2)
    rw [mul_div_cancel_left, splitFrontierTrace_append, splitFrontier_after_actual, ih, ih]

/-- The stored prefix uses the same reverse chronological convention as
`sequentialSupport`: the most recently exposed split is the head. -/
theorem splitPrefixParent_eq_foldl {G : Type*} [Div G] [One G]
    (n : ℕ) (P : G) (past : List G) :
    splitPrefixParent n P past = currentSplitParent
      (past.reverse.foldl splitFrontierStep (pendingSplitBranch n P [])) := by
  rw [splitPrefixParent, List.foldr_eq_foldl_reverse]

theorem actualSplitValues_length {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) : (actualSplitValues n x).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [actualSplitValues, List.length_cons, List.length_append, ih]
    have h := Nat.one_le_two_pow (n := n)
    rw [pow_succ]
    omega

theorem splitFrontierTrace_getD {G : Type*} [Div G] [One G]
    (frontier : List (ℕ × G)) (xs : List G) (j : ℕ) (hj : j < xs.length) :
    (splitFrontierTrace frontier xs).getD j (1, 1) =
      (currentSplitParent ((xs.take j).foldl splitFrontierStep frontier), xs.getD j 1) := by
  induction xs generalizing frontier j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [splitFrontierTrace, List.getD_cons_succ, List.take_succ_cons, List.foldl_cons] using
        ih (splitFrontierStep frontier x) j (by simpa using hj)

/-- The actual parent product at a node is a function of the initial total
and the preceding split coordinates alone, with the same prefix convention
as the arithmetic support estimator. -/
theorem actualParentSplits_from_prefix {G : Type*} [CommGroup G]
    (n : ℕ) (x : TreeLeafTuple G n) (j : ℕ) (hj : j < 2 ^ n - 1) :
    (actualParentSplits n x).getD j (1, 1) =
      (splitPrefixParent n (treeLeafProduct n x) ((actualSplitValues n x).take j).reverse,
        (actualSplitValues n x).getD j 1) := by
  rw [← splitFrontierTrace_actual n x []]
  rw [splitFrontierTrace_getD _ _ j (by simpa only [actualSplitValues_length] using hj)]
  rw [splitPrefixParent_eq_foldl, List.reverse_reverse]

end Ostmann

end OAI
