import OAI.Combinatorics.ParityLifts.CompilerBounds

namespace OAI

namespace ParityWL.Complexity

/-- A finite first-order functional language on binary trees. There are no
function-valued atoms: only projections, pairing, composition, branching and
an ordinary data-dependent loop. -/
inductive FCode where
  | id | nil | left | right
  | pair (f g : FCode)
  | seq (f g : FCode)
  | branch (nilCase nodeCase : FCode)
  | cond (test nilCase nodeCase : FCode)
  | loop (body : FCode)
  deriving DecidableEq

inductive FWhile (S : ℕ) (R : DataTree → ℕ → DataTree → Prop) :
    DataTree → ℕ → DataTree → Prop
  | stop (x) (hx : x.size ≤ S) (he : x.child false = .nil) : FWhile S R x 1 x
  | next {x y z n m} (he : x.child false ≠ .nil) (h : R x n y)
      (tail : FWhile S R y m z) : FWhile S R x (n + m + 1) z

inductive FEval (S : ℕ) : FCode → DataTree → ℕ → DataTree → Prop
  | id (x) (h : x.size ≤ S) : FEval S .id x 1 x
  | nil (x) (h : x.size ≤ S) : FEval S .nil x 1 .nil
  | left (x) (h : x.size ≤ S) : FEval S .left x 1 (x.child false)
  | right (x) (h : x.size ≤ S) : FEval S .right x 1 (x.child true)
  | pair {f g x y z n m} (hf : FEval S f x n y) (hg : FEval S g x m z)
      (hb : (DataTree.node y z).size ≤ S) : FEval S (.pair f g) x (n + m + 1) (.node y z)
  | seq {f g x y z n m} (hf : FEval S f x n y) (hg : FEval S g y m z) :
      FEval S (.seq f g) x (n + m + 1) z
  | nil_branch {f g y n} (hf : FEval S f .nil n y) : FEval S (.branch f g) .nil (n + 1) y
  | node_branch {f g x y n} (hx : x ≠ .nil) (hg : FEval S g x n y) :
      FEval S (.branch f g) x (n + 1) y
  | nil_cond {p f g x y n m} (hp : FEval S p x n .nil) (hf : FEval S f x m y) :
      FEval S (.cond p f g) x (n + m + 1) y
  | node_cond {p f g x y z n m} (hp : FEval S p x n z) (hz : z ≠ .nil)
      (hg : FEval S g x m y) : FEval S (.cond p f g) x (n + m + 1) y
  | loop_stop (f x) (hx : x.size ≤ S) (he : x.child false = .nil) :
      FEval S (.loop f) x 1 x
  | loop_next {f x y z n m} (he : x.child false ≠ .nil) (h : FEval S f x n y)
      (tail : FEval S (.loop f) y m z) : FEval S (.loop f) x (n + m + 1) z

lemma FEval.bounds {S : ℕ} {f : FCode} {x y : DataTree} {n : ℕ} (h : FEval S f x n y) :
    x.size ≤ S ∧ y.size ≤ S ∧ 0 < n := by
  induction h using FEval.rec with
  | id x h => exact ⟨h, h, by omega⟩
  | nil x h => exact ⟨h, by have := x.size_pos; simp [DataTree.size]; omega, by omega⟩
  | left x h => exact ⟨h, (x.size_child false).trans h, by omega⟩
  | right x h => exact ⟨h, (x.size_child true).trans h, by omega⟩
  | pair _ _ hb ih₁ ih₂ => exact ⟨ih₁.1, hb, by omega⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2.1, by omega⟩
  | nil_branch _ ih => exact ⟨ih.1, ih.2.1, by omega⟩
  | node_branch _ _ ih => exact ⟨ih.1, ih.2.1, by omega⟩
  | nil_cond _ _ ip hf => exact ⟨ip.1, hf.2.1, by omega⟩
  | node_cond _ _ _ ip hg => exact ⟨ip.1, hg.2.1, by omega⟩
  | loop_stop f x hx he => exact ⟨hx, hx, by omega⟩
  | loop_next he _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2.1, by omega⟩

lemma FEval.loop_iff {S : ℕ} {f : FCode} {x y : DataTree} {n : ℕ} :
    FEval S (.loop f) x n y ↔ FWhile S (FEval S f) x n y := by
  constructor
  · intro h
    induction n using Nat.strong_induction_on generalizing x y with
    | h n ih =>
      cases h with
      | loop_stop _ x hx he => exact .stop x hx he
      | loop_next he hb ht => exact .next he hb (ih _ (by omega) ht)
  · intro h
    induction h with
    | stop x hx he => exact .loop_stop f x hx he
    | next he h _ ih => exact .loop_next he h ih

def FCode.depth : FCode → ℕ
  | .id | .nil | .left | .right => 1
  | .pair f g => max (f.depth + 1) (g.depth + 2)
  | .seq f g | .branch f g => max f.depth g.depth
  | .cond p f g => max (p.depth + 1) (max f.depth g.depth)
  | .loop f => max f.depth 2

lemma FCode.depth_pos (f : FCode) : 0 < f.depth := by
  induction f <;> simp_all [FCode.depth]

def FCode.lower {r : ℕ} (f : FCode) (i : Fin r) (h : i.val + f.depth ≤ r) : TreeCode r :=
  match f with
  | .id => .skip
  | .nil => .op (.nil i)
  | .left => .op (.project i i false)
  | .right => .op (.project i i true)
  | .pair f g =>
    let j : Fin r := ⟨i.val + 1, by have := g.depth_pos; simp only [FCode.depth] at h; omega⟩
    let k : Fin r := ⟨i.val + 2, by have := g.depth_pos; simp only [FCode.depth] at h; omega⟩
    .seq (.copy j i) (.seq (f.lower j (by simp only [FCode.depth] at h; dsimp [j]; omega))
      (.seq (.copy k i) (.seq (g.lower k (by simp only [FCode.depth] at h; dsimp [k]; omega))
        (.seq (.op (.node i j k)) (.seq (.op (.nil j)) (.op (.nil k)))))))
  | .seq f g => .seq (f.lower i (by simp only [FCode.depth] at h; omega))
      (g.lower i (by simp only [FCode.depth] at h; omega))
  | .branch f g => .cond i (f.lower i (by simp only [FCode.depth] at h; omega))
      (g.lower i (by simp only [FCode.depth] at h; omega))
  | .cond p f g =>
    let j : Fin r := ⟨i.val + 1, by have := p.depth_pos; simp only [FCode.depth] at h; omega⟩
    .seq (.copy j i) (.seq (p.lower j (by dsimp [j]; simp only [FCode.depth] at h; omega))
      (.cond j (.seq (.op (.nil j)) (f.lower i (by simp only [FCode.depth] at h; omega)))
        (.seq (.op (.nil j)) (g.lower i (by simp only [FCode.depth] at h; omega)))))
  | .loop f =>
    let j : Fin r := ⟨i.val + 1, by simp only [FCode.depth] at h; omega⟩
    let body := .seq (.op (.nil j))
      (.seq (f.lower i (by simp only [FCode.depth] at h; omega)) (.op (.project j i false)))
    .seq (.op (.project j i false)) (.seq (.loop j body) (.op (.nil j)))

def FCode.factor : FCode → ℕ
  | .id | .nil | .left | .right => 2
  | .pair f g => f.factor + g.factor + 30
  | .seq f g | .branch f g => f.factor + g.factor + 1
  | .cond p f g => p.factor + f.factor + g.factor + 20
  | .loop f => f.factor + 20

lemma FCode.factor_pos (f : FCode) : 0 < f.factor := by cases f <;> simp [FCode.factor]

def CleanAbove {r : ℕ} (d : Fin r → DataTree) (i : Fin r) : Prop :=
  ∀ j, i.val < j.val → d j = .nil

lemma CleanAbove.update_self {r : ℕ} {d : Fin r → DataTree} {i : Fin r}
    (h : CleanAbove d i) (x : DataTree) : CleanAbove (Function.update d i x) i := by
  intro j hj
  have hn : j ≠ i := by intro h; subst j; omega
  simp [hn, h j hj]

lemma CleanAbove.update_later {r : ℕ} {d : Fin r → DataTree} {i j : Fin r}
    (h : CleanAbove d i) (hj : i.val < j.val) (x : DataTree) :
    CleanAbove (Function.update d j x) j := by
  intro k hk
  have hn : k ≠ j := by intro h; subst k; omega
  simp [hn, h k (by omega)]

lemma CleanAbove.erase_next {r : ℕ} {d : Fin r → DataTree} {i j : Fin r}
    (h : CleanAbove d j) (hj : j.val = i.val + 1) :
    CleanAbove (Function.update d j .nil) i := by
  intro k hk
  by_cases he : k = j
  · subst k; simp
  · have hn : j.val < k.val := by have := Fin.val_ne_of_ne he; omega
    simp [he, h k hn]

end ParityWL.Complexity

end OAI
