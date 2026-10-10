import Mathlib

namespace OAI

namespace IndependentSetsGames.Reduction.CloneGap

variable {α β : Type*}

def cart (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map fun y => (x, y)

theorem count_const (xs : List α) (b : Bool) :
    xs.countP (fun _ => b) = if b then xs.length else 0 := by
  cases b <;> simp

theorem count_cart (xs : List α) (ys : List β) (p : α → Bool) (q : β → Bool) :
    (cart xs ys).countP (fun z => p z.1 && q z.2) =
      xs.countP p * ys.countP q := by
  induction xs with
  | nil => simp [cart]
  | cons x xs ih =>
      simp only [cart, List.flatMap_cons, List.countP_append] at *
      rw [ih]
      cases h : p x <;>
        simp [List.countP_map, Function.comp_def, h, Nat.add_mul, Nat.add_comm]

theorem length_cart (xs : List α) (ys : List β) :
    (cart xs ys).length = xs.length * ys.length := by
  have := count_cart xs ys (fun _ => true) (fun _ => true)
  simpa using this

theorem count_cart_left (xs : List α) (ys : List β) (p : α → Bool) :
    (cart xs ys).countP (fun z => p z.1) = xs.countP p * ys.length := by
  simpa using count_cart xs ys p (fun _ => true)

theorem count_cart_right (xs : List α) (ys : List β) (p : β → Bool) :
    (cart xs ys).countP (fun z => p z.2) = xs.length * ys.countP p := by
  simpa using count_cart xs ys (fun _ => true) p

theorem count_cart_le (xs : List α) (ys : List β) (p : α × β → Bool)
    (bound : Nat) (h : ∀ x ∈ xs, ys.countP (fun y => p (x, y)) ≤ bound) :
    (cart xs ys).countP p ≤ xs.length * bound := by
  induction xs with
  | nil => simp [cart]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [cart, List.flatMap_cons, List.countP_append, List.countP_map,
        Function.comp_def] at *
      simp only [List.length_cons, Nat.add_mul]
      omega

theorem count_union_le (xs : List α) (p q : α → Bool) :
    xs.countP (fun x => p x || q x) ≤ xs.countP p + xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp [hp, hq] at * <;> omega

theorem count_remove (xs : List α) (p q : α → Bool) :
    xs.countP p ≤ xs.countP (fun x => p x && !q x) + xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x <;> cases hq : q x <;>
        simp [hp, hq] at * <;> omega

abbrev Index := Nat
def indices : List Index := List.range 48
def triples : List (Index × Index × Index) := cart indices (cart indices indices)
def collision (t : Index × Index × Index) : Bool :=
  (t.1 == t.2.1) || (t.1 == t.2.2) || (t.2.1 == t.2.2)
def distinctTriples : List (Index × Index × Index) := triples.filter (fun t => !collision t)

theorem length_indices : indices.length = 48 := by simp [indices]
theorem length_triples : triples.length = 110592 := by
  simp [triples, length_cart, length_indices]

theorem count_index_eq_le (i : Index) : indices.countP (fun j => i == j) ≤ 1 := by
  have h := List.count_range (a := i) (n := 48)
  have heq : (fun j => i == j) = (fun j => j == i) := by
    funext j
    exact Bool.beq_comm
  rw [heq]
  change (List.range 48).count i ≤ 1
  rw [h]
  split <;> omega

theorem count_collision_le : triples.countP collision ≤ 6912 := by
  have h12 : triples.countP (fun t => t.1 == t.2.1) ≤ 2304 := by
    apply count_cart_le indices (cart indices indices) _ 48
    intro i _
    change (cart indices indices).countP (fun y => i == y.1) ≤ 48
    rw [count_cart_left indices indices (fun j => i == j), length_indices]
    have := count_index_eq_le i
    omega
  have h13 : triples.countP (fun t => t.1 == t.2.2) ≤ 2304 := by
    apply count_cart_le indices (cart indices indices) _ 48
    intro i _
    change (cart indices indices).countP (fun y => i == y.2) ≤ 48
    rw [count_cart_right indices indices (fun j => i == j), length_indices]
    have := count_index_eq_le i
    omega
  have h23 : triples.countP (fun t => t.2.1 == t.2.2) ≤ 2304 := by
    change (cart indices (cart indices indices)).countP (fun t => t.2.1 == t.2.2) ≤ 2304
    rw [count_cart_right indices (cart indices indices) (fun t => t.1 == t.2), length_indices]
    have h : (cart indices indices).countP (fun t => t.1 == t.2) ≤ 48 := by
      apply count_cart_le indices indices _ 1
      intro i _
      exact count_index_eq_le i
    omega
  have hA := count_union_le triples (fun t => t.1 == t.2.1) (fun t => t.1 == t.2.2)
  have hB := count_union_le triples
    (fun t => (t.1 == t.2.1) || (t.1 == t.2.2)) (fun t => t.2.1 == t.2.2)
  unfold collision
  omega

theorem majority_exists (g : Index → Bool) :
    ∃ b : Bool, 24 ≤ indices.countP (fun i => g i == b) := by
  have h := List.length_eq_countP_add_countP g (l := indices)
  have hn : (fun i => decide (¬g i = true)) = (fun i => !g i) := by
    funext i
    cases g i <;> rfl
  rw [hn] at h
  rw [length_indices] at h
  by_cases ht : 24 ≤ indices.countP g
  · exact ⟨true, by simpa using ht⟩
  · refine ⟨false, ?_⟩
    have : 24 ≤ indices.countP (fun i => !g i) := by omega
    simpa using this

def allAgree (p q r : Index → Bool) (t : Index × Index × Index) : Bool :=
  p t.1 && (q t.2.1 && r t.2.2)

theorem count_agree_distinct (p q r : Index → Bool)
    (hp : 24 ≤ indices.countP p) (hq : 24 ≤ indices.countP q)
    (hr : 24 ≤ indices.countP r) :
    6912 ≤ distinctTriples.countP (allAgree p q r) := by
  have hprod := count_cart indices (cart indices indices) p
    (fun t => q t.1 && r t.2)
  rw [count_cart] at hprod
  have h1 : 24 * 24 ≤ indices.countP q * indices.countP r := Nat.mul_le_mul hq hr
  have h2 : 24 * (24 * 24) ≤ indices.countP p *
      (indices.countP q * indices.countP r) := Nat.mul_le_mul hp h1
  have hremove := count_remove triples (allAgree p q r) collision
  have hcollision := count_collision_le
  change triples.countP (allAgree p q r) = _ at hprod
  unfold distinctTriples
  rw [List.countP_filter]
  omega

structure Equation (Name : Type) where
  first : Name
  second : Name
  third : Name
  rhs : Bool

variable {Name : Type}

def satisfied (e : Equation Name) (g : Name → Bool) : Bool :=
  (xor (xor (g e.first) (g e.second)) (g e.third)) == e.rhs

def clone (e : Equation Name) (t : Index × Index × Index) : Equation (Name × Index) :=
  ⟨(e.first, t.1), (e.second, t.2.1), (e.third, t.2.2), e.rhs⟩

theorem lift_preserves (e : Equation Name) (t : Index × Index × Index) (g : Name → Bool) :
    satisfied (clone e t) (fun z => g z.1) = satisfied e g := rfl

theorem clone_names_distinct (e : Equation Name) (t : Index × Index × Index)
    (h : collision t = false) :
    (clone e t).first ≠ (clone e t).second ∧
    (clone e t).first ≠ (clone e t).third ∧
    (clone e t).second ≠ (clone e t).third := by
  simp only [collision, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  dsimp [clone]
  exact ⟨fun he => h.1.1 (congrArg Prod.snd he),
    fun he => h.1.2 (congrArg Prod.snd he),
    fun he => h.2 (congrArg Prod.snd he)⟩

theorem agree_failure (e : Equation Name) (g : Name × Index → Bool)
    (majority : Name → Bool) (t : Index × Index × Index)
    (hfail : satisfied e majority = false)
    (h : allAgree (fun i => g (e.first, i) == majority e.first)
      (fun i => g (e.second, i) == majority e.second)
      (fun i => g (e.third, i) == majority e.third) t = true) :
    satisfied (clone e t) g = false := by
  simp only [allAgree, Bool.and_eq_true, beq_iff_eq] at h
  simpa [satisfied, clone, h.1, h.2.1, h.2.2] using hfail

theorem failed_occurrence_clones (e : Equation Name) (g : Name × Index → Bool)
    (majority : Name → Bool)
    (hmaj : ∀ v, 24 ≤ indices.countP (fun i => g (v, i) == majority v))
    (hfail : satisfied e majority = false) :
    6912 ≤ distinctTriples.countP (fun t => !satisfied (clone e t) g) := by
  have h := count_agree_distinct
    (fun i => g (e.first, i) == majority e.first)
    (fun i => g (e.second, i) == majority e.second)
    (fun i => g (e.third, i) == majority e.third)
    (hmaj _) (hmaj _) (hmaj _)
  apply Nat.le_trans h
  apply List.countP_mono_left
  intro t _ ht
  have hf := agree_failure e g majority t hfail ht
  simp [hf]

def majorityBit (g : Index → Bool) : Bool := decide (24 ≤ indices.countP g)

theorem majorityBit_count (g : Index → Bool) :
    24 ≤ indices.countP (fun i => g i == majorityBit g) := by
  have h := List.length_eq_countP_add_countP g (l := indices)
  have hn : (fun i => decide (¬g i = true)) = (fun i => !g i) := by
    funext i
    cases g i <;> rfl
  rw [hn, length_indices] at h
  by_cases ht : 24 ≤ indices.countP g
  · simp [majorityBit, ht]
  · have hn : 24 ≤ indices.countP (fun i => !g i) := by omega
    simpa [majorityBit, ht] using hn

def cloneList (source : List (Equation Name)) : List (Equation (Name × Index)) :=
  source.flatMap fun e => distinctTriples.map (clone e)

theorem length_cloneList (source : List (Equation Name)) :
    (cloneList source).length = source.length * distinctTriples.length := by
  induction source with
  | nil => simp [cloneList]
  | cons e es ih =>
      simp only [cloneList, List.flatMap_cons, List.length_append, List.length_map] at *
      rw [ih]
      simp [Nat.add_mul, Nat.add_comm]

theorem cloneList_failure_lower (source : List (Equation Name))
    (g : Name × Index → Bool) (majority : Name → Bool)
    (hmaj : ∀ v, 24 ≤ indices.countP (fun i => g (v, i) == majority v)) :
    6912 * source.countP (fun e => !satisfied e majority) ≤
      (cloneList source).countP (fun e => !satisfied e g) := by
  induction source with
  | nil => simp [cloneList]
  | cons e es ih =>
      simp only [cloneList, List.flatMap_cons, List.countP_append,
        List.countP_map, Function.comp_def] at *
      cases hf : satisfied e majority with
      | false =>
          have he := failed_occurrence_clones e g majority hmaj hf
          simp [hf, Nat.mul_add] at *
          omega
      | true =>
          simp [hf]
          omega

theorem clone_gap (source : List (Equation Name))
    (source_gap : ∀ A : Name → Bool,
      source.length ≤ 4 * source.countP (fun e => !satisfied e A))
    (g : Name × Index → Bool) :
    (cloneList source).length ≤
      64 * (cloneList source).countP (fun e => !satisfied e g) := by
  let majority : Name → Bool := fun v => majorityBit (fun i => g (v, i))
  have hmaj : ∀ v, 24 ≤ indices.countP (fun i => g (v, i) == majority v) :=
    fun v => majorityBit_count (fun i => g (v, i))
  have hlocal := cloneList_failure_lower source g majority hmaj
  have hsource := source_gap majority
  have hd : distinctTriples.length ≤ 110592 := by
    exact Nat.le_trans (List.length_filter_le _ triples) (by simp [length_triples])
  rw [length_cloneList]
  have hlength := Nat.mul_le_mul_left source.length hd
  have hs := Nat.mul_le_mul_right 27648 hsource
  have hc := Nat.mul_le_mul_left 64 hlocal
  omega

theorem clone_completeness_count (source : List (Equation Name)) (A : Name → Bool) :
    (cloneList source).countP (fun e => satisfied e (fun z => A z.1)) =
      source.countP (fun e => satisfied e A) * distinctTriples.length := by
  induction source with
  | nil => simp [cloneList]
  | cons e es ih =>
      simp only [cloneList, List.flatMap_cons, List.countP_append,
        List.countP_map, Function.comp_def] at *
      rw [ih]
      have he : (fun t => satisfied (clone e t) (fun z => A z.1)) =
          (fun _ => satisfied e A) := by
        funext t
        exact lift_preserves e t A
      rw [he, count_const]
      cases h : satisfied e A <;> simp [h, Nat.add_mul, Nat.add_comm]

end IndependentSetsGames.Reduction.CloneGap

end OAI
