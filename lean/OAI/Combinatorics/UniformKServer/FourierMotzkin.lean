import Mathlib

namespace OAI

namespace UniformKServer.FourierMotzkin

structure Row (n : ℕ) where
  constant : ℚ
  coefficient : Fin n → ℚ
  deriving DecidableEq

namespace Row

def eval {n : ℕ} {K : Type*} [Field K] (r : Row n) (x : Fin n → K) : K :=
  (r.constant : K) + ∑ i, (r.coefficient i : K) * x i

def tail {n : ℕ} (r : Row (n+1)) : Row n :=
  ⟨r.constant, fun i => r.coefficient i.succ⟩

def scale {n : ℕ} (c : ℚ) (r : Row n) : Row n :=
  ⟨c*r.constant, fun i => c*r.coefficient i⟩

def sub {n : ℕ} (r s : Row n) : Row n :=
  ⟨r.constant-s.constant, fun i => r.coefficient i-s.coefficient i⟩

def bound {n : ℕ} (r : Row (n+1)) : Row n :=
  r.tail.scale (-1 / r.coefficient 0)

section Algebra
variable {n : ℕ} {K : Type*} [Field K] [CharZero K]

@[simp] theorem eval_scale (c : ℚ) (r : Row n) (x : Fin n → K) :
    (r.scale c).eval x = (c : K) * r.eval x := by
  simp only [eval, scale, Rat.cast_mul, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem eval_sub (r s : Row n) (x : Fin n → K) :
    (r.sub s).eval x = r.eval x - s.eval x := by
  simp only [eval, sub, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring

omit [CharZero K] in
@[simp] theorem eval_cons (r : Row (n+1)) (z : K) (x : Fin n → K) :
    r.eval (Fin.cons z x) = (r.coefficient 0 : K) * z + r.tail.eval x := by
  simp only [eval, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, tail]
  ring

@[simp] theorem eval_bound (r : Row (n+1)) (x : Fin n → K) :
    r.bound.eval x = - r.tail.eval x / (r.coefficient 0 : K) := by
  simp only [bound, eval_scale, Rat.cast_div, Rat.cast_neg, Rat.cast_one]
  ring

end Algebra

@[simp] theorem eval_rat_cast {n : ℕ} (r : Row n) (x : Fin n → ℚ) :
    r.eval (fun i => (x i : ℝ)) = ((r.eval x : ℚ) : ℝ) := by
  simp [eval]

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

 theorem negative_iff (r : Row (n+1)) (z : K) (x : Fin n → K)
    (h : r.coefficient 0 < 0) :
    r.eval (Fin.cons z x) ≤ 0 ↔ r.bound.eval x ≤ z := by
  have h' : (r.coefficient 0 : K) < 0 := by exact_mod_cast h
  rw [eval_cons, eval_bound, div_le_iff_of_neg h']
  constructor <;> intro H <;> nlinarith

 theorem positive_iff (r : Row (n+1)) (z : K) (x : Fin n → K)
    (h : 0 < r.coefficient 0) :
    r.eval (Fin.cons z x) ≤ 0 ↔ z ≤ r.bound.eval x := by
  have h' : (0 : K) < r.coefficient 0 := by exact_mod_cast h
  rw [eval_cons, eval_bound, le_div_iff₀ h']
  constructor <;> intro H <;> nlinarith

omit [IsStrictOrderedRing K] in
 theorem zero_iff (r : Row (n+1)) (z : K) (x : Fin n → K)
    (h : r.coefficient 0 = 0) :
    r.eval (Fin.cons z x) ≤ 0 ↔ r.tail.eval x ≤ 0 := by
  simp [h]

end Row

def lower {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => r.coefficient 0 < 0).map Row.bound

def upper {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => 0 < r.coefficient 0).map Row.bound

def independent {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => r.coefficient 0 = 0).map Row.tail

def project {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  independent R ++ (lower R).flatMap fun l => (upper R).map fun u => l.sub u

def Satisfies {n : ℕ} {K : Type*} [Field K] [LE K]
    (R : List (Row n)) (x : Fin n → K) : Prop := ∀ r ∈ R, r.eval x ≤ 0

section Projection
variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

 theorem satisfies_cons_iff (R : List (Row (n+1))) (z : K) (x : Fin n → K) :
    Satisfies R (Fin.cons z x) ↔
      Satisfies (independent R) x ∧
      (∀ l ∈ lower R, l.eval x ≤ z) ∧ (∀ u ∈ upper R, z ≤ u.eval x) := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hs, hz⟩ := List.mem_filter.mp hs
      exact (s.zero_iff z x (by simpa using hz)).mp (H s hs)
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hs, hn⟩ := List.mem_filter.mp hs
      exact (s.negative_iff z x (by simpa using hn)).mp (H s hs)
    · intro r hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hs, hp⟩ := List.mem_filter.mp hs
      exact (s.positive_iff z x (by simpa using hp)).mp (H s hs)
  · rintro ⟨hz, hl, hu⟩ r hr
    rcases lt_trichotomy (r.coefficient 0) 0 with hn | he | hp
    · apply (r.negative_iff z x hn).mpr
      apply hl r.bound
      simp only [lower, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨r, ⟨hr, hn⟩, rfl⟩
    · apply (r.zero_iff z x he).mpr
      apply hz r.tail
      simp only [independent, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨r, ⟨hr, he⟩, rfl⟩
    · apply (r.positive_iff z x hp).mpr
      apply hu r.bound
      simp only [upper, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨r, ⟨hr, hp⟩, rfl⟩

 theorem satisfies_project_iff (R : List (Row (n+1))) (x : Fin n → K) :
    Satisfies (project R) x ↔ Satisfies (independent R) x ∧
      ∀ l ∈ lower R, ∀ u ∈ upper R, l.eval x ≤ u.eval x := by
  constructor
  · intro H
    refine ⟨fun r hr => H r (List.mem_append_left _ hr), ?_⟩
    intro l hl u hu
    have hs : l.sub u ∈ project R := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨l, hl, List.mem_map.mpr ⟨u, hu, rfl⟩⟩
    simpa only [Row.eval_sub, sub_nonpos] using H (l.sub u) hs
  · rintro ⟨hz, hp⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hz r hr
    · obtain ⟨l, hl, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      simpa only [Row.eval_sub, sub_nonpos] using hp l hl u hu

 theorem project_of_satisfies (R : List (Row (n+1))) (x : Fin (n+1) → K)
    (H : Satisfies R x) : Satisfies (project R) (Fin.tail x) := by
  have hx : x = Fin.cons (x 0) (Fin.tail x) := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hx, satisfies_cons_iff] at H
  rw [satisfies_project_iff]
  exact ⟨by simpa using H.1, fun l hl u hu => le_trans (H.2.1 l hl) (H.2.2 u hu)⟩

end Projection

def high {K : Type*} [LinearOrder K] (a : K) (l : List K) : K := l.foldr max a

def low {K : Type*} [LinearOrder K] (a : K) (l : List K) : K := l.foldr min a

 theorem high_le_iff {K : Type*} [LinearOrder K] (a z : K) (l : List K) :
    high a l ≤ z ↔ a ≤ z ∧ ∀ b ∈ l, b ≤ z := by
  induction l with
  | nil => simp [high]
  | cons b l ih =>
    simp only [high, List.foldr_cons, max_le_iff] at ⊢
    change (b ≤ z ∧ high a l ≤ z) ↔ _
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

 theorem le_low_iff {K : Type*} [LinearOrder K] (a z : K) (l : List K) :
    z ≤ low a l ↔ z ≤ a ∧ ∀ b ∈ l, z ≤ b := by
  induction l with
  | nil => simp [low]
  | cons b l ih =>
    simp only [low, List.foldr_cons, le_min_iff] at ⊢
    change (z ≤ b ∧ z ≤ low a l) ↔ _
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

def intervalPivot {K : Type*} [Zero K] [LinearOrder K] (l u : List K) : K :=
  match l with
  | a :: as => high a as
  | [] => match u with
    | b :: bs => low b bs
    | [] => 0

/-- Reversing one elimination. With no lower bound choose the least upper
    bound; with no bounds choose zero, exactly as in the source. -/
def pivot {n : ℕ} {K : Type*} [Field K] [LinearOrder K]
    (R : List (Row (n+1))) (x : Fin n → K) : K :=
  intervalPivot ((lower R).map (fun r => r.eval x))
    ((upper R).map (fun r => r.eval x))

 theorem pivot_bounds {K : Type*} [Zero K] [LinearOrder K] {l u : List K}
    (H : ∀ a ∈ l, ∀ b ∈ u, a ≤ b) :
    (∀ a ∈ l, a ≤ intervalPivot l u) ∧ ∀ b ∈ u, intervalPivot l u ≤ b := by
  cases l with
  | nil =>
    simp only [List.not_mem_nil, false_implies, implies_true, true_and]
    cases u with
    | nil => simp
    | cons b bs =>
      have h := (le_low_iff b (low b bs) bs).mp (le_refl _)
      simpa only [intervalPivot, List.mem_cons, forall_eq_or_imp] using h
  | cons a as =>
    refine ⟨?_, ?_⟩
    · have h := (high_le_iff a (high a as) as).mp (le_refl _)
      simpa only [intervalPivot, List.mem_cons, forall_eq_or_imp] using h
    · intro b hb
      apply (high_le_iff a b as).mpr
      exact ⟨H a (by simp) b hb, fun x hx => H x (by simp [hx]) b hb⟩

 theorem satisfies_pivot {n : ℕ} {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (R : List (Row (n+1))) (x : Fin n → K) (H : Satisfies (project R) x) :
    Satisfies R (Fin.cons (pivot R x) x) := by
  obtain ⟨hz, hp⟩ := (satisfies_project_iff R x).mp H
  have hp' : ∀ a ∈ (lower R).map (fun r => r.eval x),
      ∀ b ∈ (upper R).map (fun r => r.eval x), a ≤ b := by
    intro a ha b hb
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hb
    exact hp l hl u hu
  have h := pivot_bounds hp'
  apply (satisfies_cons_iff R (pivot R x) x).mpr
  exact ⟨hz, fun l hl => h.1 _ (List.mem_map.mpr ⟨l, hl, rfl⟩),
    fun u hu => h.2 _ (List.mem_map.mpr ⟨u, hu, rfl⟩)⟩

/-- Exact existential projection over either ℚ or ℝ; no strict-inequality
    relaxation and no compactness or attainment assumption. -/
 theorem project_iff_exists {n : ℕ} {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (R : List (Row (n+1))) (x : Fin n → K) :
    Satisfies (project R) x ↔ ∃ z, Satisfies R (Fin.cons z x) := by
  constructor
  · intro H
    exact ⟨pivot R x, satisfies_pivot R x H⟩
  · rintro ⟨z, H⟩
    simpa only [Fin.tail_cons] using project_of_satisfies R (Fin.cons z x) H

/-- The objective is the final coordinate, retained through every projection. -/
def objective {n : ℕ} {K : Type*} (x : Fin (n+1) → K) : K := x (Fin.last n)

def baseValue (R : List (Row 1)) : ℚ :=
  high 0 ((lower R).map (fun r => r.constant))

/-- Exact rational arithmetic and comparisons only. The nonnegative objective
    constraint is imposed by the base case even if not listed among the rows. -/
def optimize : (n : ℕ) → List (Row (n+1)) → Option (Fin (n+1) → ℚ)
  | 0, R =>
    let x := Fin.cons (baseValue R) Fin.elim0
    if R.all (fun r => decide (r.eval x ≤ 0)) then some x else none
  | n+1, R => (optimize n (project R)).map (fun x => Fin.cons (pivot R x) x)

@[simp] theorem high_rat_cast (a : ℚ) (l : List ℚ) :
    ((high a l : ℚ) : ℝ) = high (a : ℝ) (l.map (fun b : ℚ => (b : ℝ))) := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa only [high, List.foldr_cons, List.map_cons, Rat.cast_max] using congrArg (max (b : ℝ)) ih

@[simp] theorem eval_empty {K : Type*} [Field K] (r : Row 0) (x : Fin 0 → K) :
    r.eval x = r.constant := by simp [Row.eval]

 theorem one_cons {K : Type*} (y : Fin 1 → K) :
    y = Fin.cons (objective y) Fin.elim0 := by
  ext i
  rw [Fin.eq_zero i]
  rfl

 theorem baseValue_nonneg (R : List (Row 1)) : 0 ≤ baseValue R :=
  ((high_le_iff 0 (baseValue R) _).mp (le_refl _)).1

 theorem baseValue_minimal (R : List (Row 1)) (y : Fin 1 → ℝ)
    (hy : 0 ≤ objective y) (hR : Satisfies R y) :
    (baseValue R : ℝ) ≤ objective y := by
  rw [one_cons y, satisfies_cons_iff] at hR
  rw [baseValue, high_rat_cast, high_le_iff]
  refine ⟨by simpa only [Rat.cast_zero] using hy, ?_⟩
  intro b hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  simpa only [eval_empty] using hR.2.1 r hr

 theorem baseValue_feasible (R : List (Row 1)) (y : Fin 1 → ℝ)
    (hy : 0 ≤ objective y) (hR : Satisfies R y) :
    Satisfies R (Fin.cons (baseValue R) (Fin.elim0 : Fin 0 → ℚ)) := by
  have hmin := baseValue_minimal R y hy hR
  rw [one_cons y, satisfies_cons_iff] at hR
  apply (satisfies_cons_iff R _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have h := hR.1 r hr
    simp only [eval_empty] at h ⊢
    exact_mod_cast h
  · intro r hr
    simp only [eval_empty]
    exact ((high_le_iff 0 (baseValue R) _).mp (le_refl _)).2
      r.constant (List.mem_map.mpr ⟨r, hr, rfl⟩)
  · intro r hr
    have h := le_trans hmin (hR.2.2 r hr)
    simp only [eval_empty] at h ⊢
    exact_mod_cast h

@[simp] theorem objective_cons {n : ℕ} {K : Type*} (a : K) (x : Fin (n+1) → K) :
    objective (Fin.cons a x) = objective x := Fin.cons_last (n := n) (α := fun _ => K) a x

@[simp] theorem objective_tail {n : ℕ} {K : Type*} (x : Fin (n+2) → K) :
    objective (Fin.tail x) = objective x := rfl

/-- The exact finite rational optimizer succeeds whenever the rational rows
have a real feasible point with nonnegative objective; its rational output is
feasible and minimizes the objective against every such real point. -/
theorem optimize_rational_attainment (n : ℕ) (R : List (Row (n+1)))
    (H : ∃ y : Fin (n+1) → ℝ, 0 ≤ objective y ∧ Satisfies R y) :
    ∃ x : Fin (n+1) → ℚ, optimize n R = some x ∧
      0 ≤ objective x ∧ Satisfies R x ∧
      ∀ y : Fin (n+1) → ℝ, 0 ≤ objective y → Satisfies R y →
        ((objective x : ℚ) : ℝ) ≤ objective y := by
  induction n with
  | zero =>
    obtain ⟨y, hy, hR⟩ := H
    have hb := baseValue_feasible R y hy hR
    have ht : R.all (fun r => decide (r.eval (Fin.cons (baseValue R) Fin.elim0) ≤ 0)) = true := by
      rw [List.all_eq_true]
      intro r hr
      exact decide_eq_true (hb r hr)
    refine ⟨Fin.cons (baseValue R) Fin.elim0, ?_, baseValue_nonneg R, hb, ?_⟩
    · simp only [optimize, ht, ↓reduceIte]
    · exact fun y hy hR => baseValue_minimal R y hy hR
  | succ n ih =>
    have HP : ∃ y : Fin (n+1) → ℝ, 0 ≤ objective y ∧ Satisfies (project R) y := by
      obtain ⟨y, hy, hR⟩ := H
      exact ⟨Fin.tail y, hy, project_of_satisfies R y hR⟩
    obtain ⟨x, hx, hn, hs, hm⟩ := ih (project R) HP
    refine ⟨Fin.cons (pivot R x) x, ?_, ?_, satisfies_pivot R x hs, ?_⟩
    · simp only [optimize, hx, Option.map_some]
    · simpa only [objective_cons] using hn
    · intro y hy hR
      simpa only [objective_cons, objective_tail] using
        hm (Fin.tail y) hy (project_of_satisfies R y hR)

end UniformKServer.FourierMotzkin

end OAI
