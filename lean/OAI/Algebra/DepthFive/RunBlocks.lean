import OAI.Algebra.DepthFive.WordRuns

namespace OAI

/-! Contiguous true blocks, with an exact block-count and product factorization. -/

open scoped BigOperators

namespace Problem335.WordRuns

variable {α : Type*}

/-- Split a list at false positions, retaining a possibly empty initial block. -/
def splitTrueAux (p : α → Bool) : List α → List α × List (List α)
  | [] => ([], [])
  | a :: l =>
    let q := splitTrueAux p l
    if p a then (a :: q.1, q.2) else ([], q.1 :: q.2)

/-- The nonempty maximal contiguous blocks of positions satisfying `p`. -/
def trueBlocks (p : α → Bool) (l : List α) : List (List α) :=
  let q := splitTrueAux p l
  (q.1 :: q.2).filter (fun b => !b.isEmpty)

@[simp] theorem splitTrueAux_fst_nil_cons (p : α → Bool) (a : α) (l : List α) :
    (splitTrueAux p (a :: l)).1 = [] ↔ p a = false := by
  cases hp : p a <;> simp [splitTrueAux, hp]

/-- The initial block is genuinely a prefix, including when empty. -/
theorem splitTrueAux_fst_prefix (p : α → Bool) (l : List α) :
    (splitTrueAux p l).1 <+: l := by
  induction l with
  | nil => simp [splitTrueAux]
  | cons a l ih =>
    cases hp : p a <;> simp [splitTrueAux, hp, ih]

/-- Splitting does not lose or duplicate any selected position. -/
theorem splitTrueAux_flatten (p : α → Bool) (l : List α) :
    (splitTrueAux p l).1 ++ (splitTrueAux p l).2.flatten = l.filter p := by
  induction l with
  | nil => simp [splitTrueAux]
  | cons a l ih =>
    cases hp : p a <;> simp [splitTrueAux, hp, ih]

@[simp] theorem trueBlocks_flatten (p : α → Bool) (l : List α) :
    (trueBlocks p l).flatten = l.filter p := by
  simpa [trueBlocks, List.flatten_filter_not_isEmpty] using splitTrueAux_flatten p l

/-- Every retained block is nonempty. -/
theorem trueBlocks_ne_nil (p : α → Bool) (l : List α) {b : List α}
    (hb : b ∈ trueBlocks p l) : b ≠ [] := by
  have h := (List.mem_filter.mp hb).2
  simpa using h

private theorem splitTrueAux_infix (p : α → Bool) (l : List α) :
    ∀ b ∈ (splitTrueAux p l).1 :: (splitTrueAux p l).2, b <:+: l := by
  induction l with
  | nil => simp [splitTrueAux]
  | cons a l ih =>
    intro b hb
    cases hp : p a with
    | false =>
      simp only [splitTrueAux, hp, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact List.nil_infix
      · exact List.infix_cons (ih _ (List.mem_cons.mpr hb))
    | true =>
      simp only [splitTrueAux, hp, ↓reduceIte, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact (show a :: (splitTrueAux p l).1 <+: a :: l from
          List.cons_prefix_cons.mpr ⟨rfl, splitTrueAux_fst_prefix p l⟩).isInfix
      · exact List.infix_cons (ih _ (List.mem_cons_of_mem _ hb))

/-- Every true block is a contiguous interval of the original ordered list. -/
theorem trueBlocks_infix (p : α → Bool) (l : List α) {b : List α}
    (hb : b ∈ trueBlocks p l) : b <:+: l :=
  splitTrueAux_infix p l b (List.mem_filter.mp hb).1

/-- Every member of a true block satisfies the selection predicate. -/
theorem trueBlocks_all_true (p : α → Bool) (l : List α) {b : List α}
    (hb : b ∈ trueBlocks p l) {a : α} (ha : a ∈ b) : p a = true := by
  have hmem : a ∈ (trueBlocks p l).flatten := List.mem_flatten.mpr ⟨b, hb, ha⟩
  rw [trueBlocks_flatten] at hmem
  exact (List.mem_filter.mp hmem).2

/-- Adding one letter either extends the first block or creates one new block. -/
theorem trueBlocks_length_cons (p : α → Bool) (a : α) (l : List α) :
    (trueBlocks p (a :: l)).length = (trueBlocks p l).length +
      if p a = true ∧ (splitTrueAux p l).1 = [] then 1 else 0 := by
  unfold trueBlocks
  cases hq : splitTrueAux p l with
  | mk r rs =>
    cases hp : p a <;> cases r <;> simp [splitTrueAux, hp, hq]

/-- For a nonempty list of word positions, block count is the true run count. -/
theorem trueBlocks_ofFn_length {n : ℕ} (w : Fin (n + 1) → Bool) :
    (trueBlocks w (List.ofFn id)).length = runCount w := by
  have hgen : ∀ (α : Type) (m : ℕ) (f : Fin (m + 1) → α) (p : α → Bool),
      (trueBlocks p (List.ofFn f)).length = runCount (p ∘ f) := by
    intro α m
    induction m with
    | zero =>
      intro f p
      simp [List.ofFn_succ, List.ofFn_zero, trueBlocks, splitTrueAux, runCount, riseCount]
      cases p (f 0) <;> rfl
    | succ m ih =>
      intro f p
      rw [List.ofFn_succ, trueBlocks_length_cons]
      change (trueBlocks p (List.ofFn (Fin.tail f))).length +
        (if p (f 0) = true ∧ (splitTrueAux p (List.ofFn (Fin.tail f))).1 = []
          then 1 else 0) = runCount (p ∘ f)
      have htail := ih (Fin.tail f) p
      rw [htail]
      have hempty : (splitTrueAux p (List.ofFn (Fin.tail f))).1 = [] ↔
          p (f 1) = false := by
        rw [List.ofFn_succ, splitTrueAux_fst_nil_cons]
        rfl
      simp only [hempty]
      have hb := rise_first_eq_fall_last (p ∘ f)
      have hbt := rise_first_eq_fall_last (p ∘ Fin.tail f)
      have hfall : fallCount (p ∘ f) =
          (if p (f 0) = true ∧ p (f 1) = false then 1 else 0) +
            fallCount (p ∘ Fin.tail f) := by
        have heq : p ∘ f = Fin.cons (p (f 0)) (p ∘ Fin.tail f) := by
          funext i
          cases i using Fin.cases <;> rfl
        rw [heq, fallCount_cons]
        rfl
      have hlast : (p ∘ Fin.tail f) (Fin.last m) = (p ∘ f) (Fin.last (m + 1)) := rfl
      unfold runCount
      rw [hlast] at hbt
      omega
  simpa using hgen (Fin (n + 1)) n (id : Fin (n + 1) → Fin (n + 1)) w

/-- Products over selected positions factor exactly into products over true blocks. -/
theorem trueBlocks_prod {R : Type*} [Monoid R] (p : α → Bool) (l : List α) (f : α → R) :
    ((l.filter p).map f).prod =
      ((trueBlocks p l).map (fun b => (b.map f).prod)).prod := by
  rw [← trueBlocks_flatten p l, List.map_flatten, List.prod_flatten, List.map_map]
  rfl

/-- A uniform bound on each interval multiplies once per true run. -/
theorem selected_prod_le_pow_runCount {n : ℕ} (w : Fin (n + 1) → Bool)
    (f : Fin (n + 1) → ℝ) (B : ℝ) (hf : ∀ i, 0 ≤ f i)
    (hB : ∀ b ∈ trueBlocks w (List.ofFn id), (b.map f).prod ≤ B) :
    (((List.ofFn id).filter w).map f).prod ≤ B ^ runCount w := by
  rw [trueBlocks_prod, ← trueBlocks_ofFn_length]
  have hnonneg : ∀ b ∈ trueBlocks w (List.ofFn id), 0 ≤ (b.map f).prod := by
    intro b hb
    apply List.prod_nonneg
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hf i
  have h := List.prod_map_le_prod_map₀ (fun b : List (Fin (n + 1)) => (b.map f).prod)
    (fun _ => B) hnonneg hB
  simpa [List.map_const, List.prod_replicate] using h

/-- Additive statistics are also exactly preserved by the block partition. -/
theorem trueBlocks_sum {R : Type*} [AddMonoid R]
    (p : α → Bool) (l : List α) (g : α → R) :
    ((l.filter p).map g).sum =
      ((trueBlocks p l).map (fun b => (b.map g).sum)).sum := by
  rw [← trueBlocks_flatten p l, List.map_flatten, List.sum_flatten, List.map_map]
  rfl

/-- Counts in any second layer partition add across the true blocks. -/
theorem trueBlocks_countP (p q : α → Bool) (l : List α) :
    ((trueBlocks p l).map (List.countP q)).sum = (l.filter p).countP q := by
  rw [← List.countP_flatten, trueBlocks_flatten]

/-- Total lengths of the runs count exactly the selected positions. -/
theorem trueBlocks_sum_length (p : α → Bool) (l : List α) :
    ((trueBlocks p l).map List.length).sum = (l.filter p).length := by
  rw [← List.length_flatten, trueBlocks_flatten]

private theorem prod_run_majorants (B : ℝ) (g : α → ℝ) (bs : List (List α)) :
    (bs.map (fun b => B * Real.exp ((b.map g).sum))).prod =
      B ^ bs.length * Real.exp (((bs.flatten).map g).sum) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.flatten_cons,
      List.map_append, List.sum_append, ih, Real.exp_add, pow_succ]
    ring

/-- Interval majorants with local exponential losses multiply once per run,
while the exponential losses add only once per selected position. -/
theorem selected_prod_le_pow_runCount_mul_exp {n : ℕ}
    (w : Fin (n + 1) → Bool) (f g : Fin (n + 1) → ℝ) (B : ℝ)
    (hf : ∀ i, 0 ≤ f i)
    (hB : ∀ b ∈ trueBlocks w (List.ofFn id),
      (b.map f).prod ≤ B * Real.exp ((b.map g).sum)) :
    (((List.ofFn id).filter w).map f).prod ≤
      B ^ runCount w * Real.exp ((((List.ofFn id).filter w).map g).sum) := by
  rw [trueBlocks_prod]
  have hnonneg : ∀ b ∈ trueBlocks w (List.ofFn id), 0 ≤ (b.map f).prod := by
    intro b hb
    apply List.prod_nonneg
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hf i
  have h := List.prod_map_le_prod_map₀ (fun b : List (Fin (n + 1)) => (b.map f).prod)
    (fun b => B * Real.exp ((b.map g).sum)) hnonneg hB
  rwa [prod_run_majorants, trueBlocks_ofFn_length, trueBlocks_flatten] at h

end Problem335.WordRuns

end OAI
