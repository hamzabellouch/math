import Mathlib

namespace OAI

section
universe u v w

namespace SourceBurnside.Tableau

abbrev Wire (n : ℕ) := Bool ⊕ Fin n

def Wire.eval {n : ℕ} (v : Fin n → Bool) : Wire n → Bool
  | .inl b => b
  | .inr i => v i

@[simp] lemma Wire.eval_map {n m : ℕ} (f : Fin n → Fin m)
    (w : Wire n) (v : Fin m → Bool) :
    Wire.eval v (Sum.map id f w) = w.eval (v ∘ f) := by
  cases w <;> rfl

def nand (a b : Bool) : Bool := !(a && b)

inductive Circuit (inputs : ℕ) : ℕ → Type
  | nil : Circuit inputs 0
  | snoc {g : ℕ} (c : Circuit inputs g) (a b : Wire (inputs + g)) :
      Circuit inputs (g + 1)

namespace Circuit

variable {I g : ℕ}

def evaluate : {g : ℕ} → Circuit I g → (Fin I → Bool) → Fin (I + g) → Bool
  | _, .nil, v => v
  | _, .snoc c a b, v => Fin.lastCases
      (nand (a.eval (c.evaluate v)) (b.eval (c.evaluate v))) (c.evaluate v)

def Satisfies : {g : ℕ} → Circuit I g → (Fin (I + g) → Bool) → Prop
  | _, .nil, _ => True
  | _, .snoc c a b, v =>
      c.Satisfies (v ∘ Fin.castSucc) ∧
      v (Fin.last _) = nand (a.eval (v ∘ Fin.castSucc)) (b.eval (v ∘ Fin.castSucc))

@[simp] theorem evaluate_input (c : Circuit I g) (v : Fin I → Bool) (i : Fin I) :
    c.evaluate v (Fin.castAdd g i) = v i := by
  induction c with
  | nil => rfl
  | snoc c a b ih =>
    change Fin.lastCases (motive := fun _ => Bool) (nand (a.eval (c.evaluate v)) (b.eval (c.evaluate v)))
      (c.evaluate v) (Fin.castSucc (Fin.castAdd _ i)) = _
    rw [Fin.lastCases_castSucc]
    exact ih

theorem evaluate_satisfies (c : Circuit I g) (v : Fin I → Bool) :
    c.Satisfies (c.evaluate v) := by
  induction c with
  | nil => trivial
  | snoc c a b ih =>
    simpa only [Satisfies, evaluate, Function.comp_def, Fin.lastCases_castSucc,
      Fin.lastCases_last, and_true] using ih

theorem assignment_unique (c : Circuit I g) (v : Fin (I + g) → Bool)
    (input : Fin I → Bool) (hv : c.Satisfies v)
    (hi : ∀ i, v (Fin.castAdd g i) = input i) : v = c.evaluate input := by
  induction c with
  | nil =>
    funext i
    exact hi i
  | snoc c a b ih =>
    have hp : v ∘ Fin.castSucc = c.evaluate input :=
      ih (v ∘ Fin.castSucc) hv.1 (fun i => hi i)
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [evaluate, Fin.lastCases_last, hp] using hv.2
    · simpa only [evaluate, Fin.lastCases_castSucc, Function.comp_def] using congrFun hp j

structure Clause (n : ℕ) where
  wires : Fin 3 → Wire n
  truth : (Fin 3 → Bool) → Bool

def Clause.Holds {n : ℕ} (c : Clause n) (v : Fin n → Bool) : Prop :=
  c.truth (fun i => (c.wires i).eval v) = true

def Clause.map {n m : ℕ} (f : Fin n → Fin m) (c : Clause n) : Clause m where
  wires i := (c.wires i).map id f
  truth := c.truth

@[simp] lemma Clause.map_holds {n m : ℕ} (f : Fin n → Fin m)
    (c : Clause n) (v : Fin m → Bool) :
    (c.map f).Holds v ↔ c.Holds (v ∘ f) := by
  simp only [Clause.Holds, Clause.map, Wire.eval_map]

def nandClauses {n : ℕ} (a b z : Wire n) : List (Clause n) :=
  [⟨![a, z, z], fun x => x 0 || x 1⟩,
   ⟨![b, z, z], fun x => x 0 || x 1⟩,
   ⟨![a, b, z], fun x => !x 0 || !x 1 || !x 2⟩]

lemma nandClauses_iff {n : ℕ} (a b z : Wire n) (v : Fin n → Bool) :
    (∀ c ∈ nandClauses a b z, c.Holds v) ↔ z.eval v = nand (a.eval v) (b.eval v) := by
  simp only [nandClauses, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, Clause.Holds, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  cases a.eval v <;> cases b.eval v <;> cases z.eval v <;> decide

def clauses : {g : ℕ} → (c : Circuit I g) → List (Clause (I + g))
  | _, .nil => []
  | _, .snoc c a b =>
      c.clauses.map (Clause.map Fin.castSucc) ++
      nandClauses (a.map id Fin.castSucc) (b.map id Fin.castSucc) (.inr (Fin.last _))

@[simp] theorem clauses_length (c : Circuit I g) : c.clauses.length = 3 * g := by
  induction c with
  | nil => rfl
  | snoc c a b ih => simp only [clauses, List.length_append, List.length_map,
      nandClauses, List.length_cons, List.length_nil, ih]; omega

theorem clauses_iff (c : Circuit I g) (v : Fin (I + g) → Bool) :
    (∀ C ∈ c.clauses, C.Holds v) ↔ c.Satisfies v := by
  induction c with
  | nil => simp [clauses, Satisfies]
  | snoc c a b ih =>
    rw [clauses, List.forall_mem_append, List.forall_mem_map, nandClauses_iff]
    simp only [Clause.map_holds, ih, Satisfies]
    cases a <;> cases b <;> rfl

end Circuit

namespace Rectangle

variable {β g : ℕ}

abbrev Bits (β : ℕ) := Fin β → Bool
abbrev Row (β : ℕ) := ℕ → Bits β

def neighborhood (row : Row β) (j : ℕ) : Fin (3 * β) → Bool := fun i =>
  let p : Fin 3 × Fin β := finProdFinEquiv.symm i
  row (j + p.1.val) p.2

variable (c : Circuit (3 * β) g) (output : Fin β → Wire (3 * β + g))

def localOutput (row : Row β) (j : ℕ) : Bits β := fun r =>
  (output r).eval (c.evaluate (neighborhood row j))

def step (W : ℕ) (blank : Bits β) (row : Row β) : Row β := fun j =>
  if 0 < j ∧ j + 1 < W then localOutput c output row (j - 1) else blank

def run (W : ℕ) (blank : Bits β) (initial : Row β) : ℕ → Row β
  | 0 => initial
  | t + 1 => step c output W blank (run W blank initial t)

def assignment (row : Row β) (j : ℕ) (gates : Fin g → Bool) :
    Fin (3 * β + g) → Bool := Fin.addCases (neighborhood row j) gates

lemma assignment_input (row : Row β) (j : ℕ) (gates : Fin g → Bool)
    (i : Fin (3 * β)) : assignment row j gates (Fin.castAdd g i) = neighborhood row j i := by
  simp only [assignment, Fin.addCases_left]

lemma assignment_evaluate (row : Row β) (j : ℕ) :
    assignment row j (fun v => c.evaluate (neighborhood row j) (Fin.natAdd (3 * β) v)) =
      c.evaluate (neighborhood row j) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp only [assignment_input, Circuit.evaluate_input]
  · simp only [assignment, Fin.addCases_right]

def Valid (T W : ℕ) (blank : Bits β) (initial : Row β)
    (X : ℕ → Row β) (Y : ℕ → ℕ → Fin g → Bool) : Prop :=
  (∀ j < W, X 0 j = initial j) ∧
  (∀ t, t + 1 < T → ∀ j < W, (j = 0 ∨ j + 1 = W) → X (t + 1) j = blank) ∧
  (∀ t, t + 1 < T → ∀ j, j + 2 < W →
    c.Satisfies (assignment (X t) j (Y t j))) ∧
  (∀ t, t + 1 < T → ∀ j, j + 2 < W → ∀ r,
    X (t + 1) (j + 1) r = (output r).eval (assignment (X t) j (Y t j)))

lemma valid_transition {T W : ℕ} {blank : Bits β} {initial : Row β}
    {X : ℕ → Row β} {Y : ℕ → ℕ → Fin g → Bool}
    (hv : Valid c output T W blank initial X Y) (t : ℕ) (ht : t + 1 < T)
    (j : ℕ) (hj : j < W) : X (t + 1) j = step c output W blank (X t) j := by
  by_cases hi : 0 < j ∧ j + 1 < W
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hk : k + 2 < W := by omega
    have he := c.assignment_unique (assignment (X t) k (Y t k))
      (neighborhood (X t) k) (hv.2.2.1 t ht k hk) (assignment_input _ _ _)
    funext r
    simpa only [step, ite_eq_left hi, localOutput, Nat.succ_eq_add_one, Nat.add_sub_cancel, he] using
      hv.2.2.2 t ht k hk r
  · rw [step, ite_eq_right hi]
    exact hv.2.1 t ht j hj (by omega)

theorem valid_run {T W : ℕ} {blank : Bits β} {initial : Row β}
    {X : ℕ → Row β} {Y : ℕ → ℕ → Fin g → Bool}
    (hv : Valid c output T W blank initial X Y) (t : ℕ) (ht : t < T)
    (j : ℕ) (hj : j < W) : X t j = run c output W blank initial t j := by
  induction t generalizing j with
  | zero => exact hv.1 j hj
  | succ t ih =>
    rw [valid_transition c output hv t ht j hj, run]
    by_cases hi : 0 < j ∧ j + 1 < W
    · have hn : neighborhood (X t) (j - 1) =
          neighborhood (run c output W blank initial t) (j - 1) := by
        funext i
        dsimp only [neighborhood]
        apply congrFun (ih (by omega) _ (by
          have hh : (finProdFinEquiv.symm i : Fin 3 × Fin β).1.val < 3 :=
            (finProdFinEquiv.symm i : Fin 3 × Fin β).1.isLt
          omega))
      simp only [step, ite_eq_left hi]
      unfold localOutput
      rw [hn]
    · simp only [step, ite_eq_right hi]

theorem run_valid (T W : ℕ) (blank : Bits β) (initial : Row β) :
    Valid c output T W blank initial (run c output W blank initial)
      (fun t j v => c.evaluate (neighborhood (run c output W blank initial t) j)
        (Fin.natAdd (3 * β) v)) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro t ht j hj he
    rw [run, step, ite_eq_right (by omega)]
  · intro t ht j hj
    rw [assignment_evaluate]
    exact c.evaluate_satisfies _
  · intro t ht j hj r
    rw [assignment_evaluate]
    simp only [run, step, ite_eq_left (show 0 < j + 1 ∧ j + 1 + 1 < W by omega),
      Nat.add_sub_cancel, localOutput]

theorem accepting_tableau_iff (T W origin : ℕ) (hT : 0 < T) (hO : origin < W)
    (blank accept : Bits β) (initial : Row β) :
    (∃ X Y, Valid c output T W blank initial X Y ∧ X (T - 1) origin = accept) ↔
      run c output W blank initial (T - 1) origin = accept := by
  constructor
  · rintro ⟨X, Y, hv, ha⟩
    rw [← valid_run c output hv (T - 1) (by omega) origin hO]
    exact ha
  · intro ha
    exact ⟨_, _, run_valid c output T W blank initial, ha⟩

end Rectangle

namespace Layout

def certificateCount (β g T W : ℕ) : ℕ := β * W * T + g * (W - 2) * (T - 1)

def clauseCount (β g T W : ℕ) : ℕ :=
  2 * β * W + 2 * β * (T - 1) + (3 * g + 2 * β) * (W - 2) * (T - 1) + β

def xAddress (β W t j r : ℕ) : ℕ := β * (W * t + j) + r

def yAddress (β g T W t j v : ℕ) : ℕ :=
  β * W * T + g * ((W - 2) * t + j) + v

lemma pack_lt {A B a b : ℕ} (ha : a < A) (hb : b < B) : B * a + b < B * A := by
  calc B * a + b < B * a + B := Nat.add_lt_add_left hb _
    _ = B * (a + 1) := by ring
    _ ≤ B * A := Nat.mul_le_mul_left B ha

lemma pack_injective {B a a' b b' : ℕ} (hB : 0 < B) (hb : b < B) (hb' : b' < B)
    (he : B * a + b = B * a' + b') : a = a' ∧ b = b' := by
  have hbb : b = b' := by
    have hh := congrArg (· % B) he
    simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] using hh
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hB
    exact Nat.add_right_cancel (he.trans (by rw [hbb]))
  · exact hbb

lemma xAddress_lt {β T W t j r : ℕ} (ht : t < T) (hj : j < W) (hr : r < β) :
    xAddress β W t j r < β * W * T := by
  simpa only [xAddress, Nat.mul_assoc] using pack_lt (pack_lt ht hj) hr

lemma yAddress_lt {β g T W t j v : ℕ} (ht : t < T - 1) (hj : j < W - 2)
    (hv : v < g) : yAddress β g T W t j v < certificateCount β g T W := by
  have hh := pack_lt (pack_lt ht hj) hv
  unfold yAddress certificateCount
  nlinarith

lemma xAddress_injective {β W t t' j j' r r' : ℕ}
    (hj : j < W) (hj' : j' < W) (hr : r < β) (hr' : r' < β)
    (he : xAddress β W t j r = xAddress β W t' j' r') :
    t = t' ∧ j = j' ∧ r = r' := by
  obtain ⟨h1, h2⟩ := pack_injective (by omega) hr hr' he
  obtain ⟨h3, h4⟩ := pack_injective (by omega) hj hj' h1
  exact ⟨h3, h4, h2⟩

lemma yAddress_injective {β g T W t t' j j' v v' : ℕ}
    (hj : j < W - 2) (hj' : j' < W - 2) (hv : v < g) (hv' : v' < g)
    (he : yAddress β g T W t j v = yAddress β g T W t' j' v') :
    t = t' ∧ j = j' ∧ v = v' := by
  have he' : g * ((W - 2) * t + j) + v = g * ((W - 2) * t' + j') + v' := by
    unfold yAddress at he
    omega
  obtain ⟨h1, h2⟩ := pack_injective (by omega) hv hv' he'
  obtain ⟨h3, h4⟩ := pack_injective (by omega) hj hj' h1
  exact ⟨h3, h4, h2⟩

lemma address_disjoint {β g T W t j r : ℕ} (ht : t < T) (hj : j < W) (hr : r < β)
    (t' j' v : ℕ) : xAddress β W t j r ≠ yAddress β g T W t' j' v := by
  have hh := xAddress_lt ht hj hr
  unfold yAddress
  omega

lemma rectangle_le (a T : ℕ) : a * (4 * T - 2) * (T - 1) ≤ 4 * a * T ^ 2 := by
  calc a * (4 * T - 2) * (T - 1) ≤ a * (4 * T) * T :=
      Nat.mul_le_mul (Nat.mul_le_mul_left a (Nat.sub_le _ _)) (Nat.sub_le _ _)
    _ = 4 * a * T ^ 2 := by ring

lemma certificateCount_bound (β g T : ℕ) :
    certificateCount β g T (4 * T) ≤ (20 * β + 12 * g + 1) * T ^ 2 := by
  have hh := rectangle_le g T
  unfold certificateCount
  nlinarith

lemma clauseCount_bound (β g T : ℕ) (hT : 0 < T) :
    clauseCount β g T (4 * T) ≤ (20 * β + 12 * g + 1) * T ^ 2 := by
  have hh := rectangle_le (3 * g + 2 * β) T
  have h2 : T ≤ T ^ 2 := by nlinarith
  have h3 : 1 ≤ T ^ 2 := by nlinarith
  have h4 := Nat.mul_le_mul_left (10 * β) h2
  have h5 := Nat.mul_le_mul_left β h3
  have h6 := Nat.mul_le_mul_left (2 * β) (Nat.sub_le T 1)
  unfold clauseCount
  nlinarith

lemma exponential_margin (C h : ℕ) (hh : 5 * C ≤ h) :
    C * (2 ^ (h / 5)) ^ 2 ≤ 2 ^ h := by
  have hr : C ≤ h / 5 := (Nat.le_div_iff_mul_le (by omega : 0 < 5)).mpr (by omega)
  have hC : C ≤ 2 ^ (h / 5) := (Nat.lt_two_pow_self (n := C)).le.trans (Nat.pow_le_pow_right (by omega) hr)
  calc C * (2 ^ (h / 5)) ^ 2 ≤ 2 ^ (h / 5) * (2 ^ (h / 5)) ^ 2 :=
      Nat.mul_le_mul_right _ hC
    _ = 2 ^ (3 * (h / 5)) := by rw [← pow_mul, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) (by
      have hd := Nat.div_mul_le_self h 5
      omega)

theorem layout_fits (β g h : ℕ) (hh : 5 * (20 * β + 12 * g + 1) ≤ h) :
    let T := 2 ^ (h / 5)
    certificateCount β g T (4 * T) ≤ 2 ^ h ∧ clauseCount β g T (4 * T) ≤ 2 ^ h := by
  dsimp only
  have he := exponential_margin (20 * β + 12 * g + 1) h hh
  exact ⟨(certificateCount_bound β g _).trans he,
    (clauseCount_bound β g _ (by positivity)).trans he⟩

end Layout

end SourceBurnside.Tableau

end

end OAI
