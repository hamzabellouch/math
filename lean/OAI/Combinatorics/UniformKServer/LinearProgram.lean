import Mathlib
import OAI.Combinatorics.UniformKServer.OfflineDynamic
import OAI.Combinatorics.UniformKServer.FourierMotzkin

namespace OAI

namespace UniformKServer.EffectiveLP
open FourierMotzkin

/-- Computable increasing-code enumeration. No finite-choice oracle. -/
def enumerate {A : Type*} [Fintype A] [Encodable A] : List A :=
  letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  Finset.univ.sort (· ≤ ·)

def index (A : Type*) [Fintype A] [Encodable A] : A ≃ Fin (Fintype.card A) :=
  letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  (Fintype.orderIsoFinOfCardEq A rfl).toEquiv.symm

theorem mem_enumerate {A : Type*} [Fintype A] [Encodable A] (a : A) :
    a ∈ (enumerate : List A) := by
  simp [enumerate]


/-- Exactly the finite source word-prefix set, explicitly enumerated. -/
def words (n : ℕ) : ℕ → Finset (List (Fin n))
  | 0 => {[]}
  | H+1 => insert [] (Finset.univ.biUnion fun r => (words n H).image (r::·))

def Word (n H : ℕ) := {w : List (Fin n) // w ∈ words n H}
instance (n H : ℕ) : Fintype (Word n H) := inferInstanceAs (Fintype {w // w ∈ words n H})
instance (n H : ℕ) : DecidableEq (Word n H) := inferInstanceAs (DecidableEq {w // w ∈ words n H})
instance (n H : ℕ) : Encodable (Word n H) := inferInstanceAs (Encodable {w // w ∈ words n H})

def Config (n k : ℕ) := {c : Configuration n k // Function.Injective c}
instance (n k : ℕ) : Fintype (Config n k) := inferInstanceAs (Fintype {c : Configuration n k // Function.Injective c})
instance (n k : ℕ) : DecidableEq (Config n k) := inferInstanceAs (DecidableEq {c : Configuration n k // Function.Injective c})
instance (n k : ℕ) : Encodable (Config n k) := inferInstanceAs (Encodable {c : Configuration n k // Function.Injective c})

/-- The source allowed-label set, not a relaxed transition relation. -/
def labels {n k : ℕ} (c : Config n k) (r : Fin n) : Finset (Fin k) :=
  if ∃ j, c.val j = r then Finset.univ.filter (fun j => c.val j = r) else Finset.univ

def Label {n k : ℕ} (c : Config n k) (r : Fin n) := {j : Fin k // j ∈ labels c r}
instance {n k : ℕ} (c : Config n k) (r : Fin n) : Fintype (Label c r) :=
  inferInstanceAs (Fintype {j // j ∈ labels c r})
instance {n k : ℕ} (c : Config n k) (r : Fin n) : DecidableEq (Label c r) :=
  inferInstanceAs (DecidableEq {j // j ∈ labels c r})
instance {n k : ℕ} (c : Config n k) (r : Fin n) : Encodable (Label c r) :=
  inferInstanceAs (Encodable {j // j ∈ labels c r})

def Short (n H : ℕ) := {w : Word n H // w.val.length < H}
instance (n H : ℕ) : Fintype (Short n H) := inferInstanceAs (Fintype {w : Word n H // w.val.length < H})
instance (n H : ℕ) : DecidableEq (Short n H) := inferInstanceAs (DecidableEq {w : Word n H // w.val.length < H})
instance (n H : ℕ) : Encodable (Short n H) := inferInstanceAs (Encodable {w : Word n H // w.val.length < H})

-- A finite free variable for each displayed source p and allowed f.
abbrev Edge (n k H : ℕ) := (_ : Short n H) × (r : Fin n) × (c : Config n k) × Label c r
abbrev Variable (n k H : ℕ) := (Word n H × Config n k) ⊕ Edge n k H

structure BoundedFlow (n k H : ℕ) (K : Type*) where
  mass : Word n H → Config n k → K
  flow : (w : Short n H) → (r : Fin n) → (c : Config n k) → Label c r → K

def toAssignment {n k H : ℕ} {K : Type*} (F : BoundedFlow n k H K) : Variable n k H → K
  | .inl (w,c) => F.mass w c
  | .inr ⟨w,r,c,j⟩ => F.flow w r c j

def ofAssignment {n k H : ℕ} {K : Type*} (x : Variable n k H → K) : BoundedFlow n k H K where
  mass w c := x (.inl (w,c))
  flow w r c j := x (.inr ⟨w,r,c,j⟩)

namespace Form
variable {V : Type*} [Fintype V] [DecidableEq V] [Encodable V]

abbrev RowV (V : Type*) [Fintype V] := Row (Fintype.card V + 1)

def var (v : V) : RowV V :=
  ⟨0, fun i => if i = (index V v).castSucc then 1 else 0⟩
def objective : RowV V := ⟨0, fun i => if i = Fin.last (Fintype.card V) then 1 else 0⟩
def constant (a : ℚ) : RowV V := ⟨a, fun _ => 0⟩
def sum {I : Type*} (S : Finset I) (f : I → RowV V) : RowV V :=
  ⟨∑ i ∈ S, (f i).constant, fun j => ∑ i ∈ S, (f i).coefficient j⟩

def eqRows (f : RowV V) : List (RowV V) := [f, f.scale (-1)]
def vector {K : Type*} (x : V → K) (a : K) : Fin (Fintype.card V + 1) → K :=
  Fin.lastCases a (fun i => x ((index V).symm i))
def recover {K : Type*} (x : Fin (Fintype.card V + 1) → K) : V → K :=
  fun v => x ((index V v).castSucc)
end Form

theorem mem_words {n H : ℕ} (w : List (Fin n)) : w ∈ words n H ↔ w.length ≤ H := by
  induction H generalizing w with
  | zero => simp [words]
  | succ H ih =>
    cases w with
    | nil => simp [words]
    | cons r w =>
      simp only [words, Finset.mem_insert, List.cons_ne_nil, false_or, Finset.mem_biUnion,
        Finset.mem_univ, true_and, Finset.mem_image, List.cons.injEq, List.length_cons]
      constructor
      · rintro ⟨r',w',hw',hr,hw⟩
        subst r'; subst w'
        exact Nat.succ_le_succ ((ih w).mp hw')
      · intro hw
        exact ⟨r,w,(ih w).mpr (Nat.le_of_succ_le_succ hw),rfl,rfl⟩

theorem label_injective {n k : ℕ} (c : Config n k) (r : Fin n) (j : Label c r) :
    Function.Injective (serve c.val r j.val) := by
  classical
  have hj := j.property
  unfold labels at hj
  split_ifs at hj with hh
  · have he : c.val j.val = r := (Finset.mem_filter.mp hj).2
    have hs : serve c.val r j.val = c.val := by
      unfold serve
      conv_lhs => arg 3; rw [← he]
      exact Function.update_eq_self _ _
    rw [hs]
    exact c.property
  · intro a b hab
    by_cases ha : a = j.val
    · subst a
      by_cases hb : b = j.val
      · exact hb.symm
      · simp only [serve, Function.update_self, Function.update_of_ne hb] at hab
        exact (hh ⟨b,hab.symm⟩).elim
    · by_cases hb : b = j.val
      · subst b
        simp only [serve, Function.update_self, Function.update_of_ne ha] at hab
        exact (hh ⟨a,hab⟩).elim
      · simp only [serve, Function.update_of_ne ha, Function.update_of_ne hb] at hab
        exact c.property hab

def step {n k : ℕ} (c : Config n k) (r : Fin n) (j : Label c r) : Config n k :=
  ⟨serve c.val r j.val, label_injective c r j⟩

def rootWord (n H : ℕ) : Word n H := ⟨[], (mem_words []).mpr (Nat.zero_le _)⟩
def extend {n H : ℕ} (w : Short n H) (r : Fin n) : Word n H :=
  ⟨w.val.val++[r], (mem_words _).mpr (by simpa using w.property)⟩

def prefixNode {n H : ℕ} (w : Word n H) (i : Fin w.val.length) : Short n H :=
  ⟨⟨w.val.take i, (mem_words _).mpr
    (by simp only [List.length_take]; exact (Nat.min_le_right _ _).trans ((mem_words _).mp w.property))⟩,
    by have hw := (mem_words _).mp w.property
       simp only [List.length_take]
       omega⟩

abbrev Row (n k H : ℕ) := FourierMotzkin.Row (Fintype.card (Variable n k H)+1)

def massRow {n k H : ℕ} (w : Word n H) (c : Config n k) : Row n k H :=
  Form.var (.inl (w,c))
def flowRow {n k H : ℕ} (w : Short n H) (r : Fin n)
    (c : Config n k) (j : Label c r) : Row n k H :=
  Form.var (.inr ⟨w,r,c,j⟩)

def costRow {n k H : ℕ} (d : RationalMetric n) (w : Word n H) : Row n k H :=
  Form.sum Finset.univ fun i : Fin w.val.length =>
    Form.sum Finset.univ fun c : Config n k =>
      Form.sum Finset.univ fun j : Label c w.val[i] =>
        (flowRow (prefixNode w i) w.val[i] c j).scale (d.distance (c.val j.val) w.val[i])

def constraints {n k H : ℕ} [NeZero k] (d : RationalMetric n)
    (u : Config n k) : List (Row n k H) :=
  [Form.objective.scale (-1)] ++
  (enumerate.flatMap fun wc : Word n H × Config n k => [(massRow wc.1 wc.2).scale (-1)]) ++
  (enumerate.flatMap fun w : Word n H =>
    Form.eqRows ((Form.sum Finset.univ (massRow w)).sub (Form.constant 1))) ++
  (enumerate.flatMap fun c : Config n k =>
    Form.eqRows ((massRow (rootWord n H) c).sub (Form.constant (if c = u then 1 else 0)))) ++
  (enumerate.flatMap fun e : Edge n k H => [(flowRow e.1 e.2.1 e.2.2.1 e.2.2.2).scale (-1)]) ++
  (enumerate.flatMap fun w : Short n H =>
    enumerate.flatMap fun r : Fin n =>
      enumerate.flatMap fun c : Config n k =>
        Form.eqRows ((Form.sum Finset.univ (flowRow w r c)).sub (massRow w.val c))) ++
  (enumerate.flatMap fun w : Short n H =>
    enumerate.flatMap fun r : Fin n =>
      enumerate.flatMap fun c' : Config n k =>
        Form.eqRows ((Form.sum Finset.univ fun c : Config n k =>
          Form.sum Finset.univ fun j : Label c r =>
            if step c r j = c' then flowRow w r c j else Form.constant 0).sub (massRow (extend w r) c')) ) ++
  (enumerate.flatMap fun w : Word n H =>
    [(costRow d w).sub (Form.objective.scale (OfflineDynamic.optRat d u.val w.val))])

-- Exact interpretation of the source constraints, over either rationals or reals.
def Valid {n k H : ℕ} {K : Type*} [Field K] [LinearOrder K]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H K) (a : K)
    [NeZero k] : Prop :=
  0 ≤ a ∧
  (∀ w c, 0 ≤ F.mass w c) ∧
  (∀ w, ∑ c, F.mass w c = 1) ∧
  (∀ c, F.mass (rootWord n H) c = if c = u then 1 else 0) ∧
  (∀ w r c j, 0 ≤ F.flow w r c j) ∧
  (∀ w r c, ∑ j, F.flow w r c j = F.mass w.val c) ∧
  (∀ w r c', (∑ c, ∑ j, if step c r j = c' then F.flow w r c j else 0) = F.mass (extend w r) c') ∧
  (∀ w, (∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
     F.flow (prefixNode w i) w.val[i] c j * (d.distance (c.val j.val) w.val[i] : K)) ≤
       a * (OfflineDynamic.optRat d u.val w.val : K))

namespace Form
variable {V : Type*} [Fintype V] {K : Type*}

theorem recover_vector [Encodable V] (x : V → K) (a : K) : recover (vector x a) = x := by
  funext v
  simp [recover, vector]

theorem objective_vector [Encodable V] (x : V → K) (a : K) :
    FourierMotzkin.objective (vector x a) = a := by
  simp [FourierMotzkin.objective, vector]

variable [Field K]

theorem eval_var [Encodable V] (v : V) (x : Fin (Fintype.card V+1) → K) :
    (var v).eval x = recover x v := by
  classical
  simp [var, FourierMotzkin.Row.eval, recover, ite_mul, apply_ite]

theorem eval_objective (x : Fin (Fintype.card V+1) → K) :
    (objective (V := V)).eval x = FourierMotzkin.objective x := by
  simp [objective, FourierMotzkin.objective, FourierMotzkin.Row.eval, ite_mul, apply_ite]

theorem eval_constant (a : ℚ) (x : Fin (Fintype.card V+1) → K) :
    (constant (V := V) a).eval x = (a : K) := by
  simp [constant, FourierMotzkin.Row.eval]

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem eval_sum {I : Type*} (S : Finset I) (f : I → RowV V)
    (x : Fin (Fintype.card V+1) → K) :
    (sum S f).eval x = ∑ i ∈ S, (f i).eval x := by
  simp only [sum, FourierMotzkin.Row.eval, Rat.cast_sum, Finset.sum_mul,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]

theorem eqRows_iff (f : RowV V) (x : Fin (Fintype.card V+1) → K) :
    Satisfies (eqRows f) x ↔ f.eval x = 0 := by
  simp only [Satisfies, eqRows, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, FourierMotzkin.Row.eval_scale,
    Rat.cast_neg, Rat.cast_one, neg_one_mul]
  constructor
  · rintro ⟨ha,hb⟩
    exact le_antisymm ha (neg_nonpos.mp hb)
  · intro hh
    simp [hh]

end Form

theorem satisfies_append {m : ℕ} {K : Type*} [Field K] [LE K]
    (R S : List (FourierMotzkin.Row m)) (x : Fin m → K) :
    Satisfies (R++S) x ↔ Satisfies R x ∧ Satisfies S x := by
  constructor
  · intro h
    exact ⟨fun r hr => h r (List.mem_append_left S hr), fun r hr => h r (List.mem_append_right R hr)⟩
  · rintro ⟨hR,hS⟩ r hr
    exact (List.mem_append.mp hr).elim (hR r) (hS r)

theorem satisfies_flatMap {m : ℕ} {I K : Type*} [Fintype I] [Encodable I] [Field K] [LE K]
    (f : I → List (FourierMotzkin.Row m)) (x : Fin m → K) :
    Satisfies (enumerate.flatMap f) x ↔ ∀ i, Satisfies (f i) x := by
  simp only [Satisfies, List.mem_flatMap, mem_enumerate, true_and, forall_exists_index]
  exact forall_comm

theorem satisfies_singleton {m : ℕ} {K : Type*} [Field K] [LE K]
    (r : FourierMotzkin.Row m) (x : Fin m → K) : Satisfies [r] x ↔ r.eval x ≤ 0 := by
  simp [Satisfies]

theorem eval_costRow {n k H : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (d : RationalMetric n) (w : Word n H) (x : Fin (Fintype.card (Variable n k H)+1) → K) :
    (costRow d w).eval x =
      ∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
        (ofAssignment (Form.recover x)).flow (prefixNode w i) w.val[i] c j *
          (d.distance (c.val j.val) w.val[i] : K) := by
  simp only [costRow, Form.eval_sum, FourierMotzkin.Row.eval_scale, flowRow, Form.eval_var,
    ofAssignment]
  congr 1
  funext i
  congr 1
  funext c
  congr 1
  funext j
  exact mul_comm _ _

theorem eval_if {m : ℕ} {K : Type*} [Field K] (p : Prop) [Decidable p]
    (f g : FourierMotzkin.Row m) (x : Fin m → K) :
    (if p then f else g).eval x = if p then f.eval x else g.eval x := by
  split_ifs <;> rfl

theorem constraints_iff {n k H : ℕ} [NeZero k] {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (d : RationalMetric n) (u : Config n k)
    (x : Fin (Fintype.card (Variable n k H)+1) → K) :
    Satisfies (constraints d u) x ↔
      Valid d u (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) := by
  classical
  unfold constraints
  simp only [satisfies_append, satisfies_flatMap, satisfies_singleton, Form.eqRows_iff]
  simp only [and_assoc]
  change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_scale, Form.eval_objective,
      Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_nonpos]
  apply and_congr
  · simp only [Prod.forall, FourierMotzkin.Row.eval_scale, Rat.cast_neg,
      Rat.cast_one, neg_one_mul, neg_nonpos, massRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, Form.eval_constant,
      Rat.cast_one, sub_eq_zero, massRow, Form.eval_var, ofAssignment]
  apply and_congr
  · apply forall_congr'
    intro c
    by_cases hc : c = u <;>
      simp only [hc, ite_true, ite_false, FourierMotzkin.Row.eval_sub,
        Form.eval_constant, sub_eq_zero, massRow, Form.eval_var, ofAssignment,
        Rat.cast_one, Rat.cast_zero]
  apply and_congr
  · simp only [Sigma.forall, FourierMotzkin.Row.eval_scale, Rat.cast_neg,
      Rat.cast_one, neg_one_mul, neg_nonpos, flowRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, sub_eq_zero,
      massRow, flowRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, sub_eq_zero,
      massRow, flowRow, Form.eval_var, ofAssignment, eval_if, Form.eval_constant,
      Rat.cast_zero]
  · simp only [FourierMotzkin.Row.eval_sub, eval_costRow, sub_nonpos,
      FourierMotzkin.Row.eval_scale, Form.eval_objective, mul_comm]

theorem rational_attainment {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k)
    (h : ∃ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u F a) :
    ∃ x : Fin (Fintype.card (Variable n k H)+1) → ℚ,
      optimize (Fintype.card (Variable n k H)) (constraints d u) = some x ∧
      Valid d u (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) ∧
      ∀ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u F a →
        ((FourierMotzkin.objective x : ℚ) : ℝ) ≤ a := by
  have build (F : BoundedFlow n k H ℝ) (a : ℝ) (hF : Valid d u F a) :
      Satisfies (constraints d u) (Form.vector (toAssignment F) a) := by
    apply (constraints_iff d u _).mpr
    simpa only [Form.recover_vector, Form.objective_vector, toAssignment, ofAssignment] using hF
  obtain ⟨F,a,ha⟩ := h
  have hex : ∃ y : Fin (Fintype.card (Variable n k H)+1) → ℝ,
      0 ≤ FourierMotzkin.objective y ∧ Satisfies (constraints d u) y :=
    ⟨Form.vector (toAssignment F) a, by simpa only [Form.objective_vector] using ha.1, build F a ha⟩
  obtain ⟨x,hx,hn,hs,hm⟩ := optimize_rational_attainment _ (constraints d u) hex
  refine ⟨x,hx,(constraints_iff d u x).mp hs, ?_⟩
  intro F a ha
  simpa only [Form.objective_vector] using hm (Form.vector (toAssignment F) a)
    (by simpa only [Form.objective_vector] using ha.1) (build F a ha)

end UniformKServer.EffectiveLP


end OAI
