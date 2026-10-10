import Mathlib.Data.Fintype.Sum
import Std
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {Name : Type u} {Id : Type v} {R : Type w}
variable {k : Nat}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

inductive Record (Name : Type u) (Id : Type v) (R : Type w)
  | blank
  | single (name : Name) (coefficient : R)
  | full (occurrence : Id) (coefficients : Fin 3 → R)
  deriving DecidableEq

def recordEquiv : Record Name Id R ≃ Unit ⊕ ((Name × R) ⊕ (Id × (Fin 3 → R))) where
  toFun r := match r with
    | .blank => .inl ()
    | .single n c => .inr (.inl (n,c))
    | .full e a => .inr (.inr (e,a))
  invFun r := match r with
    | .inl _ => .blank
    | .inr (.inl (n,c)) => .single n c
    | .inr (.inr (e,a)) => .full e a
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with u | (p | p) <;> cases ‹_› <;> rfl

noncomputable instance [Fintype Name] [Fintype Id] [Fintype R] :
    Fintype (Record Name Id R) := Fintype.ofEquiv _ recordEquiv.symm

abbrev Data (k : Nat) (Name : Type u) (Id : Type v) (R : Type w) :=
  R × (Fin k → Record Name Id R)

def pivot (a : Fin 3 → R) : R :=
  if a 0 = a 1 then a 0 else if a 0 = a 2 then a 0 else a 2

def translate (a : Fin 3 → R) (t : R) : Fin 3 → R := fun i => a i + t
def normalize (a : Fin 3 → R) : Fin 3 → R := translate a (pivot a)

def record (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) :
    Record Name Id R :=
  if a 0 = a 1 then
      if a 0 = a 2 then .blank else .single (names e 2) (a 2 + a 0)
    else if a 0 = a 2 then .single (names e 1) (a 1 + a 0)
    else if a 1 = a 2 then .single (names e 0) (a 0 + a 2)
    else .full e (normalize a)

def data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) : Data k Name Id R :=
  (z + ∑ j, rhs (occ j) • pivot (a j), fun j => record names (occ j) (a j))

def standardTriple (X : E k →ₗ[F2] R) (j : Fin k) : Fin 3 → R :=
  ![X (firstBasis j), X (secondBasis j), 0]

def canonical (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (X : E k →ₗ[F2] R) : Data k Name Id R :=
  data occ names rhs (X (hBasis k)) (standardTriple X)

def ambientEval (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) (x : E k) : R :=
  x.1 • z + ∑ j, ((x.2 j).1 • a j 0 + (x.2 j).2 • a j 1 +
    (b j * x.1 + (x.2 j).1 + (x.2 j).2) • a j 2)

def Represents (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) : Prop := ∀ x, ambientEval b z a x = X x

omit [DecidableEq R] in
theorem add_self (x : R) : x + x = 0 := by
  calc
    x + x = (1 + 1 : F2) • x := by simp [add_smul]
    _ = 0 := by rw [show (1 + 1 : F2) = 0 by decide, zero_smul]

omit [DecidableEq R] in
theorem add_both (x y t : R) : (x + t) + (y + t) = x + y := by
  calc
    _ = (x + y) + (t + t) := by abel
    _ = _ := by rw [add_self, add_zero]

omit [Module F2 R] in
theorem pivot_translate (a : Fin 3 → R) (t : R) :
    pivot (translate a t) = pivot a + t := by
  classical
  by_cases h1 : a 0 = a 1 <;> by_cases h2 : a 0 = a 2 <;>
    simp [pivot, translate, h1, h2]

theorem normalize_translate (a : Fin 3 → R) (t : R) :
    normalize (translate a t) = normalize a := by
  unfold normalize
  rw [pivot_translate]
  funext i
  exact add_both _ _ _

theorem record_translate (names : Id → Fin 3 → Name) (e : Id) (a : Fin 3 → R) (t : R) :
    record names e (translate a t) = record names e a := by
  classical
  have hs (i : Fin 3) : translate a t i = a i + t := rfl
  simp only [record, hs, add_right_cancel_iff, add_both, normalize_translate]

theorem data_gauge (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z : R) (a : Fin k → Fin 3 → R) (t : Fin k → R) :
    data occ names rhs (z + ∑ j, rhs (occ j) • t j) (fun j => translate (a j) (t j)) =
      data occ names rhs z a := by
  apply Prod.ext
  · simp only [data, pivot_translate, smul_add, Finset.sum_add_distrib]
    exact add_both _ _ _
  · funext j
    exact record_translate names (occ j) (a j) (t j)

theorem data_global_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (z c : R) (a : Fin k → Fin 3 → R) :
    data occ names rhs (z + c) a =
      ((data occ names rhs z a).1 + c, (data occ names rhs z a).2) := by
  apply Prod.ext
  · dsimp [data]; abel
  · rfl

theorem canonical_shift (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (X : E k →ₗ[F2] R) (c : R) :
    canonical occ names rhs (X + tau.smulRight c) =
      ((canonical occ names rhs X).1 + c, (canonical occ names rhs X).2) := by
  have ht : standardTriple (X + tau.smulRight c) = standardTriple X := by
    funext j i
    fin_cases i <;> simp [standardTriple, tau, firstBasis, secondBasis]
  simp only [canonical, ht]
  have hg : (X + tau.smulRight c : E k →ₗ[F2] R) (hBasis k) = X (hBasis k) + c := by
    simp [hBasis, tau]
  rw [hg]
  exact data_global_shift occ names rhs _ c _

omit [DecidableEq R] in
@[simp] theorem ambientEval_hBasis (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R) :
    ambientEval b z a (hBasis k) = z + ∑ j, b j • a j 2 := by
  simp [ambientEval, hBasis]

omit [DecidableEq R] in
@[simp] theorem ambientEval_firstBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (firstBasis j) = a j 0 + a j 2 := by
  classical
  simp only [ambientEval, firstBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in
@[simp] theorem ambientEval_secondBasis (b : Fin k → F2) (z : R)
    (a : Fin k → Fin 3 → R) (j : Fin k) :
    ambientEval b z a (secondBasis j) = a j 1 + a j 2 := by
  classical
  simp only [ambientEval, secondBasis, zero_smul, zero_add, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

omit [DecidableEq R] in
/-- Every actual linear map has the claimed ambient coefficient extension. -/
theorem standard_represents (b : Fin k → F2) (X : E k →ₗ[F2] R) :
    Represents b (X (hBasis k)) (standardTriple X) X := by
  intro x
  simpa [ambientEval, standardTriple] using (linearMap_expansion X x).symm

omit [DecidableEq R] in
/-- Equality on the homogeneous space forces the free-coordinate identities. -/
theorem extension_coefficients (b : Fin k → F2) (z : R) (a : Fin k → Fin 3 → R)
    (X : E k →ₗ[F2] R) (h : Represents b z a X) :
    X (hBasis k) = z + ∑ j, b j • a j 2 ∧
      ∀ j, X (firstBasis j) = a j 0 + a j 2 ∧
        X (secondBasis j) = a j 1 + a j 2 := by
  constructor
  · simpa only [ambientEval_hBasis] using (h (hBasis k)).symm
  · intro j
    exact ⟨by simpa only [ambientEval_firstBasis] using (h (firstBasis j)).symm,
      by simpa only [ambientEval_secondBasis] using (h (secondBasis j)).symm⟩

/-- Every ambient extension of a genuine map gives the same canonical data. -/
theorem canonical_eq_of_extension (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z : R) (a : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X) :
    canonical occ names rhs X = data occ names rhs z a := by
  obtain ⟨hz, ha⟩ := extension_coefficients _ z a X h
  have ht : standardTriple X = fun j => translate (a j) (a j 2) := by
    funext j i
    fin_cases i
    · exact (ha j).1
    · exact (ha j).2
    · exact (add_self (a j 2)).symm
  unfold canonical
  rw [hz, ht]
  exact data_gauge occ names rhs z a (fun j => a j 2)

theorem extension_independent (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (z z' : R) (a a' : Fin k → Fin 3 → R) (X : E k →ₗ[F2] R)
    (h : Represents (fun j => rhs (occ j)) z a X)
    (h' : Represents (fun j => rhs (occ j)) z' a' X) :
    data occ names rhs z a = data occ names rhs z' a' :=
  (canonical_eq_of_extension occ names rhs z a X h).symm.trans
    (canonical_eq_of_extension occ names rhs z' a' X h')

def singletonTriple (i : Fin 3) (c : R) : Fin 3 → R := Pi.single i c

omit [Module F2 R] in
theorem pivot_singleton (i : Fin 3) (c : R) : pivot (singletonTriple i c) = 0 := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;> simp [singletonTriple, pivot, hc]

omit [Module F2 R] in
theorem record_singleton (names : Id → Fin 3 → Name) (e : Id) (i : Fin 3) (c : R) :
    record names e (singletonTriple i c) =
      (if c = 0 then Record.blank else Record.single (names e i) c) := by
  classical
  by_cases hc : c = 0 <;> fin_cases i <;>
    simp [record, singletonTriple, hc, eq_comm]

theorem singleton_global_adjustment (rhs : Id → F2) (e : Id) (i : Fin 3) (c : R) :
    rhs e • pivot (singletonTriple i c) = 0 := by rw [pivot_singleton, smul_zero]

omit [Module F2 R] in
/-- The hidden occurrence and its internal slot cannot affect a retained
single-variable record. The occurrence need not differ from other positions. -/
theorem singleton_locality (names : Id → Fin 3 → Name) (e e' : Id)
    (i i' : Fin 3) (c : R) (hname : names e i = names e' i') :
    record names e (singletonTriple i c) = record names e' (singletonTriple i' c) := by
  simp only [record_singleton, hname]

end UniqueGamesTheorem.Reduction.ActualCanonical

end

section

namespace UniqueGamesTheorem.Reduction.CloneGap

variable {α : Type*} {β : Type*} {Name : Type}

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

end UniqueGamesTheorem.Reduction.CloneGap

end

end OAI
