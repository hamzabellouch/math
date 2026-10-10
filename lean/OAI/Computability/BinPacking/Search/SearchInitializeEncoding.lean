import Lean.Elab.Tactic.Omega
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.Machines.MachineBoundedIteration
import OAI.Computability.BinPacking.Machines.MachineKeepDecisionTyped
import OAI.Computability.BinPacking.Packing.PackingGapDefinitions

namespace OAI

namespace BinPackingGap.ExtensionQuery

def Agrees (fixed : List (Option Nat)) (assignments : List Nat) : Prop :=
  fixed.length = assignments.length ∧
    ∀ (i j : Nat), fixed[i]? = some (some j) → assignments[i]? = some j

def Ext (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) : Prop :=
  items.Valid ∧ ∃ assignments : List Nat,
    (RawPacking.mk bins assignments).Feasible items ∧ Agrees fixed assignments

@[simp] theorem agrees_nil_left (assignments : List Nat) :
    Agrees [] assignments ↔ assignments = [] := by
  cases assignments with
  | nil => simp [Agrees]
  | cons head tail => simp [Agrees]

@[simp] theorem agrees_nil_right (fixed : List (Option Nat)) :
    Agrees fixed [] ↔ fixed = [] := by
  cases fixed with
  | nil => simp [Agrees]
  | cons head tail => simp [Agrees]

theorem agrees_cons (entry : Option Nat) (fixed : List (Option Nat))
    (label : Nat) (assignments : List Nat) :
    Agrees (entry :: fixed) (label :: assignments) ↔
      (entry = none ∨ entry = some label) ∧ Agrees fixed assignments := by
  constructor
  · rintro ⟨lengths, agrees⟩
    refine ⟨?_, Nat.succ.inj lengths, ?_⟩
    · cases entry with
      | none => exact Or.inl rfl
      | some value =>
          right
          have equal : label = value := by simpa using agrees 0 value rfl
          exact congrArg some equal.symm
    · intro i j fixedAt
      simpa using agrees (i + 1) j (by simpa using fixedAt)
  · rintro ⟨head, lengths, tail⟩
    refine ⟨congrArg Nat.succ lengths, ?_⟩
    intro i j fixedAt
    cases i with
    | zero =>
        have entryAt : entry = some j := by simpa using fixedAt
        rcases head with head | head
        · rw [head] at entryAt
          cases entryAt
        · have equal : label = j := Option.some.inj (head.symm.trans entryAt)
          simpa using congrArg some equal
    | succ i =>
        simpa using tail i j (by simpa using fixedAt)

@[simp] theorem agrees_replicate_none (n : Nat) (assignments : List Nat) :
    Agrees (List.replicate n none) assignments ↔ n = assignments.length := by
  induction n generalizing assignments with
  | zero => simp [eq_comm]
  | succ n ih =>
      cases assignments with
      | nil => simp
      | cons label assignments =>
          simp [List.replicate_succ, agrees_cons, ih]

@[simp] theorem agrees_map_some (fixed assignments : List Nat) :
    Agrees (fixed.map some) assignments ↔ fixed = assignments := by
  induction fixed generalizing assignments with
  | nil => simp [eq_comm]
  | cons label fixed ih =>
      cases assignments with
      | nil => simp
      | cons other assignments =>
          simp [agrees_cons, ih]

theorem ext_none_iff (bins : Nat) (items : RawInstance) :
    Ext bins items (List.replicate items.length none) ↔
      items.Valid ∧ ∃ assignments : List Nat,
        (RawPacking.mk bins assignments).Feasible items := by
  constructor
  · rintro ⟨valid, assignments, feasible, _⟩
    exact ⟨valid, assignments, feasible⟩
  · rintro ⟨valid, assignments, feasible⟩
    refine ⟨valid, assignments, feasible, ?_⟩
    exact (agrees_replicate_none items.length assignments).mpr feasible.1.symm

theorem ext_full_iff (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    Ext bins items (assignments.map some) ↔
      items.Valid ∧ (RawPacking.mk bins assignments).Feasible items := by
  constructor
  · rintro ⟨valid, submitted, feasible, agrees⟩
    have equal := (agrees_map_some assignments submitted).mp agrees
    subst submitted
    exact ⟨valid, feasible⟩
  · rintro ⟨valid, feasible⟩
    exact ⟨valid, assignments, feasible,
      (agrees_map_some assignments assignments).mpr rfl⟩

theorem ext_fixed_length {bins : Nat} {items : RawInstance}
    {fixed : List (Option Nat)} (extension : Ext bins items fixed) :
    fixed.length = items.length := by
  obtain ⟨_, assignments, feasible, agrees⟩ := extension
  exact agrees.1.trans feasible.1

theorem ext_iff_exists_packing (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    Ext bins items fixed ↔
      ∃ valid : items.Valid, ∃ packing : Packing (items.toInstance valid) bins,
        Agrees fixed (List.ofFn fun i => (packing.assignment i).val) := by
  constructor
  · rintro ⟨valid, assignments, feasible, agrees⟩
    obtain ⟨packing, same⟩ :=
      (RawPacking.feasible_iff_exists_packing items valid ⟨bins, assignments⟩).mp feasible
    change assignments = List.ofFn (fun i => (packing.assignment i).val) at same
    refine ⟨valid, packing, ?_⟩
    simpa only [same] using agrees
  · rintro ⟨valid, packing, agrees⟩
    refine ⟨valid, List.ofFn (fun i => (packing.assignment i).val), ?_, agrees⟩
    apply (RawPacking.feasible_iff_exists_packing items valid
      ⟨bins, List.ofFn (fun i => (packing.assignment i).val)⟩).mpr
    exact ⟨packing, rfl⟩

theorem ext_none_iff_hasPacking (bins : Nat) (items : RawInstance) (valid : items.Valid) :
    Ext bins items (List.replicate items.length none) ↔
      HasPacking (items.toInstance valid) bins := by
  rw [ext_none_iff, RawPacking.hasPacking_iff_exists_feasible items valid bins]
  exact ⟨fun h => h.2, fun h => ⟨valid, h⟩⟩

end BinPackingGap.ExtensionQuery

namespace BinPackingGap.SearchSemantics

open ExtensionQuery

private theorem get_some_of_lt {α : Type*} (xs : List α) (i : Nat)
    (hi : i < xs.length) : ∃ x, xs[i]? = some x := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => exact ⟨x, rfl⟩
      | succ i => simpa using ih i (by simpa using hi)

private theorem mem_of_get_some {α : Type*} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil => simp at h
  | cons y ys ih =>
      cases i with
      | zero =>
          have hyx : y = x := by simpa using h
          subst x
          simp
      | succ i => exact List.mem_cons_of_mem y (ih h)

private theorem get_set_same {α : Type*} (xs : List α) (i : Nat) (x : α)
    (hi : i < xs.length) : (xs.set i x)[i]? = some x := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i (by simpa using hi)

private theorem get_set_other {α : Type*} (xs : List α) (i j : Nat) (x : α)
    (hij : j ≠ i) : (xs.set i x)[j]? = xs[j]? := by
  induction xs generalizing i j with
  | nil => simp
  | cons y ys ih =>
      cases i <;> cases j <;> simp_all

def Prefix (i : Nat) (fixed : List (Option Nat)) : Prop :=
  (∀ t < i, ∃ j, fixed[t]? = some (some j)) ∧
  (∀ t, i ≤ t → t < fixed.length → fixed[t]? = some none)

theorem prefix_none (n : Nat) : Prefix 0 (List.replicate n none) := by
  constructor
  · intro t ht
    omega
  · intro t _ ht
    have ht' : t < n := by simpa using ht
    simp [ht']

theorem prefix_set {fixed : List (Option Nat)} {i : Nat}
    (hp : Prefix i fixed) (hi : i < fixed.length) (j : Nat) :
    Prefix (i + 1) (fixed.set i (some j)) := by
  constructor
  · intro t ht
    by_cases hti : t = i
    · subst t
      exact ⟨j, get_set_same fixed i (some j) hi⟩
    · obtain ⟨q, hq⟩ := hp.1 t (by omega)
      exact ⟨q, (get_set_other fixed i t (some j) hti).trans hq⟩
  · intro t ht hlen
    rw [get_set_other fixed i t (some j) (by omega)]
    exact hp.2 t (by omega) (by simpa using hlen)

theorem agrees_set {fixed : List (Option Nat)} {a : List Nat} {i j : Nat}
    (ha : Agrees fixed a) (hi : i < fixed.length) (hij : a[i]? = some j) :
    Agrees (fixed.set i (some j)) a := by
  refine ⟨by simpa using ha.1, ?_⟩
  intro t q hq
  by_cases hti : t = i
  · subst t
    rw [get_set_same fixed i (some j) hi] at hq
    have : j = q := by simpa using hq
    simpa [this] using hij
  · exact ha.2 t q ((get_set_other fixed i t (some j) hti).symm.trans hq)

theorem ext_next_exists {b : Nat} {r : RawInstance} {fixed : List (Option Nat)}
    (he : Ext b r fixed) {i : Nat} (hi : i < fixed.length) :
    ∃ j < b, Ext b r (fixed.set i (some j)) := by
  rcases he with ⟨hr, a, hfeas, ha⟩
  have hlen := ha.1
  obtain ⟨j, hj⟩ := get_some_of_lt a i (by omega)
  refine ⟨j, hfeas.2.1 j (mem_of_get_some hj), hr, a, hfeas, ?_⟩
  exact agrees_set ha hi hj

def labels (fixed : List (Option Nat)) : List Nat :=
  fixed.map (fun x => x.getD 0)

private theorem labels_eq_of_complete {fixed : List (Option Nat)} {a : List Nat}
    (ha : Agrees fixed a) (hp : Prefix fixed.length fixed) : labels fixed = a := by
  have hlen := ha.1
  apply List.ext_getElem?
  intro i
  by_cases hi : i < fixed.length
  · obtain ⟨j, hj⟩ := hp.1 i hi
    have haj := ha.2 i j hj
    simp [labels, List.getElem?_map, hj, haj]
  · have hai : a.length ≤ i := by omega
    have hfi : fixed.length ≤ i := by omega
    simp [labels, List.getElem?_map,
      List.getElem?_eq_none hai, List.getElem?_eq_none hfi]

theorem ext_complete {b : Nat} {r : RawInstance} {fixed : List (Option Nat)}
    (he : Ext b r fixed) (hp : Prefix fixed.length fixed) :
    RawPacking.Feasible r ⟨b, labels fixed⟩ := by
  obtain ⟨_, a, hfeas, ha⟩ := he
  simpa only [labels_eq_of_complete ha hp] using hfeas

inductive Phase where
  | find | fill | done | invalid
  deriving DecidableEq, Repr

structure State where
  items : RawInstance
  phase : Phase
  bins : Nat
  item : Nat
  label : Nat
  fixed : List (Option Nat)
  deriving DecidableEq, Repr

def initial (r : RawInstance) (valid : Bool) : State :=
  if valid then
    if r.length = 0 then ⟨r, .done, 0, 0, 0, []⟩
    else ⟨r, .find, 1, 0, 0, List.replicate r.length none⟩
  else ⟨r, .invalid, 0, 0, 0, []⟩

def query (s : State) : List Bool :=
  match s.phase with
  | .find => BinaryEncoding.extensionBits s.bins s.items s.fixed
  | .fill => BinaryEncoding.extensionBits s.bins s.items
      (s.fixed.set s.item (some s.label))
  | .done | .invalid => []

def update (s : State) (answer : Bool) : State :=
  match s.phase with
  | .find =>
      if answer then { s with phase := .fill, item := 0, label := 0 }
      else { s with bins := s.bins + 1 }
  | .fill =>
      if answer then
        { s with phase := if s.item + 1 = s.items.length then .done else .fill
                 item := s.item + 1, label := 0
                 fixed := s.fixed.set s.item (some s.label) }
      else { s with label := s.label + 1 }
  | .done | .invalid => s

def step (D : List Bool → Bool) (s : State) : State := update s (D (query s))

def run (D : List Bool → Bool) : Nat → State → State
  | 0, s => s
  | t + 1, s => run D t (step D s)

theorem run_eq_iterate (D : List Bool → Bool) (t : Nat) (s : State) :
    run D t s = (step D)^[t] s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      simpa only [run, Function.iterate_succ_apply] using ih (step D s)

def queryTrace (D : List Bool → Bool) : Nat → State → List (List Bool)
  | 0, _ => []
  | t + 1, s => query s :: queryTrace D t (step D s)

theorem queryTrace_length (D : List Bool → Bool) (t : Nat) (s : State) :
    (queryTrace D t s).length = t := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih => simp only [queryTrace, List.length_cons, ih]

def fuel (r : RawInstance) : Nat := r.length * (r.length + 1)

def output (s : State) : Option RawPacking :=
  match s.phase with
  | .done => some ⟨s.bins, labels s.fixed⟩
  | _ => none

def search (D : List Bool → Bool) (r : RawInstance) (valid : Bool) : Option RawPacking :=
  output (run D (if valid then fuel r else 0) (initial r valid))

def DecidesExtension (D : List Bool → Bool) : Prop :=
  ∀ b r fixed, D (BinaryEncoding.extensionBits b r fixed) = true ↔ Ext b r fixed

@[simp] theorem update_items (s : State) (answer : Bool) :
    (update s answer).items = s.items := by
  cases h : s.phase <;> cases answer <;> simp [update, h]

@[simp] theorem step_done (D : List Bool → Bool) (s : State) (h : s.phase = .done) :
    step D s = s := by simp [step, update, h]

@[simp] theorem step_invalid (D : List Bool → Bool) (s : State) (h : s.phase = .invalid) :
    step D s = s := by simp [step, update, h]

theorem run_done (D : List Bool → Bool) (s : State) (h : s.phase = .done) (t : Nat) :
    run D t s = s := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [run, step_done D s h] using ih

theorem run_invalid (D : List Bool → Bool) (s : State) (h : s.phase = .invalid)
    (t : Nat) : run D t s = s := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [run, step_invalid D s h] using ih

theorem ext_none_opt_iff (r : RawInstance) (hr : r.Valid) (b : Nat) :
    Ext b r (List.replicate r.length none) ↔ opt (r.toInstance hr) ≤ b := by
  rw [ext_none_iff]
  constructor
  · rintro ⟨_, ha⟩
    exact opt_le_of_hasPacking
      ((RawPacking.hasPacking_iff_exists_feasible r hr b).mpr ha)
  · intro hb
    exact ⟨hr, (RawPacking.hasPacking_iff_exists_feasible r hr b).mp
      ((hasPacking_iff_opt_le (r.toInstance hr) b).mpr hb)⟩

theorem opt_pos (r : RawInstance) (hr : r.Valid) (hn : 0 < r.length) :
    0 < opt (r.toInstance hr) := by
  obtain ⟨p⟩ := opt_attained (r.toInstance hr)
  have := (p.assignment ⟨0, hn⟩).isLt
  omega

structure FindInvariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop where
  bins_pos : 0 < s.bins
  bins_le : s.bins ≤ opt (r.toInstance hr)
  item_zero : s.item = 0
  label_zero : s.label = 0
  fixed_none : s.fixed = List.replicate r.length none

structure FillInvariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop where
  bins_eq : s.bins = opt (r.toInstance hr)
  bins_pos : 0 < s.bins
  item_lt : s.item < r.length
  label_lt : s.label < s.bins
  fixed_length : s.fixed.length = r.length
  «prefix» : Prefix s.item s.fixed
  «extends» : Ext s.bins r s.fixed
  rejected : ∀ j < s.label, ¬ Ext s.bins r (s.fixed.set s.item (some j))

structure DoneInvariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop where
  bins_eq : s.bins = opt (r.toInstance hr)
  item_eq : s.item = r.length
  label_zero : s.label = 0
  fixed_length : s.fixed.length = r.length
  «prefix» : Prefix r.length s.fixed
  «extends» : Ext s.bins r s.fixed

def Invariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop :=
  s.items = r ∧ match s.phase with
  | .find => FindInvariant r hr s
  | .fill => FillInvariant r hr s
  | .done => DoneInvariant r hr s
  | .invalid => False

theorem find_smaller_infeasible {r : RawInstance} {hr : r.Valid} {s : State}
    (hs : FindInvariant r hr s) {b : Nat} (hb : b < s.bins) :
    ¬ Ext b r (List.replicate r.length none) := by
  intro he
  have hopt := (ext_none_opt_iff r hr b).mp he
  have := hs.bins_le
  omega

theorem initial_invariant (r : RawInstance) (hr : r.Valid) :
    Invariant r hr (initial r true) := by
  by_cases hn : r.length = 0
  · have ho := opt_eq_zero_of_n_eq_zero (r.toInstance hr) hn
    have he : Ext 0 r [] := by
      simpa [hn] using (ext_none_opt_iff r hr 0).mpr (by omega)
    have hi : initial r true = ⟨r, .done, 0, 0, 0, []⟩ := by simp [initial, hn]
    rw [hi]
    refine ⟨rfl, ?_⟩
    change DoneInvariant r hr ⟨r, .done, 0, 0, 0, []⟩
    exact ⟨ho.symm, hn.symm, rfl, hn.symm,
      by simpa [hn] using prefix_none 0, he⟩
  · have ho := opt_pos r hr (by omega)
    have hi : initial r true = ⟨r, .find, 1, 0, 0, List.replicate r.length none⟩ := by
      simp [initial, hn]
    rw [hi]
    refine ⟨rfl, ?_⟩
    change FindInvariant r hr ⟨r, .find, 1, 0, 0, List.replicate r.length none⟩
    exact ⟨by change 0 < 1; decide, by dsimp; omega, rfl, rfl, rfl⟩

theorem step_invariant {D : List Bool → Bool} (hD : DecidesExtension D)
    {r : RawInstance} {hr : r.Valid} {s : State} (hs : Invariant r hr s) :
    Invariant r hr (step D s) := by
  rcases hs with ⟨hitems, hs⟩
  refine ⟨(update_items s (D (query s))).trans hitems, ?_⟩
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | done =>
      simpa only [step_done D s hp, hp] using hs
  | find =>
      simp only [hp] at hs
      change FindInvariant r hr s at hs
      have hbinspos := hs.bins_pos
      have hquery : query s =
          BinaryEncoding.extensionBits s.bins r (List.replicate r.length none) := by
        simp [query, hp, hitems, hs.fixed_none]
      by_cases ha : D (query s) = true
      · have he := (hD s.bins r (List.replicate r.length none)).mp
          (by simpa only [hquery] using ha)
        have hopt := (ext_none_opt_iff r hr s.bins).mp he
        have hb : s.bins = opt (r.toInstance hr) := Nat.le_antisymm hs.bins_le hopt
        have hn : 0 < r.length := lt_of_lt_of_le hs.bins_pos
          (hs.bins_le.trans (opt_le_n (r.toInstance hr)))
        simp only [step, update, hp, ha, ↓reduceIte]
        refine ⟨hb, hs.bins_pos, hn, hs.bins_pos, ?_, ?_, ?_, ?_⟩
        · simp [hs.fixed_none]
        · simpa [hs.fixed_none] using prefix_none r.length
        · simpa [hs.fixed_none] using he
        · intro j hj
          change j < 0 at hj
          omega
      · have hno : ¬ Ext s.bins r (List.replicate r.length none) := by
          intro he
          exact ha (by simpa only [hquery] using
            (hD s.bins r (List.replicate r.length none)).mpr he)
        have hb : s.bins + 1 ≤ opt (r.toInstance hr) := by
          have := mt (ext_none_opt_iff r hr s.bins).mpr hno
          omega
        simp only [step, update, hp, ha, Bool.false_eq_true, ↓reduceIte]
        exact ⟨by dsimp; omega, hb, hs.item_zero, hs.label_zero, hs.fixed_none⟩
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hitem := hs.item_lt
      have hlength := hs.fixed_length
      have hquery : query s = BinaryEncoding.extensionBits s.bins r
          (s.fixed.set s.item (some s.label)) := by simp [query, hp, hitems]
      by_cases ha : D (query s) = true
      · have he := (hD s.bins r (s.fixed.set s.item (some s.label))).mp
          (by simpa only [hquery] using ha)
        have hpref := prefix_set hs.prefix
          (show s.item < s.fixed.length by omega) s.label
        by_cases hlast : s.item + 1 = r.length
        · simp only [step, update, hp, ha, hitems, hlast, ↓reduceIte]
          exact ⟨hs.bins_eq, rfl, rfl, by simpa using hs.fixed_length,
            by simpa [hlast] using hpref, he⟩
        · simp only [step, update, hp, ha, hitems, hlast, ↓reduceIte]
          refine ⟨hs.bins_eq, hs.bins_pos, by dsimp; omega, hs.bins_pos,
            by simpa using hs.fixed_length, hpref, he, ?_⟩
          intro j hj
          change j < 0 at hj
          omega
      · have hno : ¬ Ext s.bins r (s.fixed.set s.item (some s.label)) := by
          intro he
          exact ha (by simpa only [hquery] using
            (hD s.bins r (s.fixed.set s.item (some s.label))).mpr he)
        obtain ⟨q, hqb, hqe⟩ := ext_next_exists hs.extends
          (show s.item < s.fixed.length by omega)
        have hlq : s.label ≤ q := by
          by_contra h
          exact hs.rejected q (by omega) hqe
        have hneq : q ≠ s.label := by
          intro h
          exact hno (h ▸ hqe)
        have hlabel : s.label + 1 < s.bins := by omega
        simp only [step, update, hp, ha, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs.bins_eq, hs.bins_pos, hs.item_lt, hlabel, hs.fixed_length,
          hs.prefix, hs.extends, ?_⟩
        intro j hj he
        change j < s.label + 1 at hj
        by_cases hjl : j < s.label
        · exact hs.rejected j hjl he
        · have hje : j = s.label := by omega
          exact hno (hje ▸ he)

private theorem index_of_mem {α : Type*} {x : α} {xs : List α} (hx : x ∈ xs) :
    ∃ i : Nat, xs[i]? = some x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst y
        exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := ih h
        exact ⟨i + 1, hi⟩

theorem ext_label_lt {b : Nat} {r : RawInstance} {fixed : List (Option Nat)}
    (he : Ext b r fixed) {j : Nat} (hj : some j ∈ fixed) : j < b := by
  obtain ⟨_, a, hfeas, ha⟩ := he
  obtain ⟨i, hi⟩ := index_of_mem hj
  exact hfeas.2.1 j (mem_of_get_some (ha.2 i j hi))

theorem invariant_bounds {r : RawInstance} {hr : r.Valid} {s : State}
    (hs : Invariant r hr s) :
    s.items = r ∧ s.bins ≤ r.length ∧ s.item ≤ r.length ∧ s.label ≤ r.length ∧
      s.fixed.length = r.length ∧ ∀ j, some j ∈ s.fixed → j < r.length := by
  rcases hs with ⟨hitems, hs⟩
  refine ⟨hitems, ?_⟩
  have hopt := opt_le_n (r.toInstance hr)
  change opt (r.toInstance hr) ≤ r.length at hopt
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | find =>
      simp only [hp] at hs
      change FindInvariant r hr s at hs
      have hitem := hs.item_zero
      have hlabel := hs.label_zero
      refine ⟨hs.bins_le.trans hopt, by omega, by omega, ?_, ?_⟩
      · simp [hs.fixed_none]
      · intro j hj
        simp [hs.fixed_none] at hj
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hbins := hs.bins_eq
      have hlabel := hs.label_lt
      have hb : s.bins ≤ r.length := by omega
      refine ⟨hb, Nat.le_of_lt hs.item_lt, by omega, hs.fixed_length, ?_⟩
      intro j hj
      exact lt_of_lt_of_le (ext_label_lt hs.extends hj) hb
  | done =>
      simp only [hp] at hs
      change DoneInvariant r hr s at hs
      have hbins := hs.bins_eq
      have hitem := hs.item_eq
      have hlabel := hs.label_zero
      have hb : s.bins ≤ r.length := by omega
      refine ⟨hb, by omega, by omega, hs.fixed_length, ?_⟩
      intro j hj
      exact lt_of_lt_of_le (ext_label_lt hs.extends hj) hb

def rank (s : State) : Nat :=
  match s.phase with
  | .find => s.items.length * s.items.length + (s.items.length + 1 - s.bins)
  | .fill => (s.items.length - s.item) * s.bins - s.label
  | .done | .invalid => 0

theorem rank_pos {r : RawInstance} {hr : r.Valid} {s : State}
    (hs : Invariant r hr s) (hd : s.phase ≠ .done) : 0 < rank s := by
  have hb := (invariant_bounds hs).2.1
  rcases hs with ⟨hitems, hs⟩
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | done => exact False.elim (hd hp)
  | find =>
      simp only [rank, hp, hitems]
      omega
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hitem := hs.item_lt
      have hm : s.bins ≤ (r.length - s.item) * s.bins := by
        simpa using Nat.mul_le_mul_right s.bins
          (show 1 ≤ r.length - s.item by omega)
      simp only [rank, hp, hitems]
      have := hs.label_lt
      omega

theorem rank_step_lt {D : List Bool → Bool} {r : RawInstance} {hr : r.Valid}
    {s : State} (hs : Invariant r hr s) (hd : s.phase ≠ .done) :
    rank (step D s) < rank s := by
  have hb := (invariant_bounds hs).2.1
  rcases hs with ⟨hitems, hs⟩
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | done => exact False.elim (hd hp)
  | find =>
      simp only [hp] at hs
      change FindInvariant r hr s at hs
      by_cases ha : D (query s) = true
      · have hm := Nat.mul_le_mul_left r.length hb
        simp only [rank, step, update, hp, ha, ↓reduceIte, hitems, Nat.sub_zero]
        omega
      · simp only [rank, step, update, hp, ha, Bool.false_eq_true, ↓reduceIte, hitems]
        omega
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hitem := hs.item_lt
      have hm : s.bins ≤ (r.length - s.item) * s.bins := by
        simpa using Nat.mul_le_mul_right s.bins
          (show 1 ≤ r.length - s.item by omega)
      have hlabel := hs.label_lt
      by_cases ha : D (query s) = true
      · have hsub : r.length - s.item = (r.length - (s.item + 1)) + 1 := by omega
        have hmul : (r.length - s.item) * s.bins =
            (r.length - (s.item + 1)) * s.bins + s.bins := by
          rw [hsub, Nat.add_mul]
          simp
        by_cases hlast : s.item + 1 = r.length
        · simp only [rank, step, update, hp, ha, hitems, hlast, ↓reduceIte]
          omega
        · simp only [rank, step, update, hp, ha, hitems, hlast, ↓reduceIte,
            Nat.sub_zero]
          omega
      · simp only [rank, step, update, hp, ha, Bool.false_eq_true, ↓reduceIte, hitems]
        omega

theorem rank_initial_le (r : RawInstance) : rank (initial r true) ≤ fuel r := by
  by_cases hn : r.length = 0
  · simp [rank, initial, hn, fuel]
  · simp [rank, initial, hn, fuel, Nat.mul_add, Nat.add_comm]

theorem run_finishes {D : List Bool → Bool} (hD : DecidesExtension D)
    {r : RawInstance} {hr : r.Valid} {s : State} (hs : Invariant r hr s)
    (t : Nat) (ht : rank s ≤ t) :
    (run D t s).phase = .done ∧ Invariant r hr (run D t s) := by
  induction t generalizing s with
  | zero =>
      have hd : s.phase = .done := by
        by_contra hd
        have := rank_pos hs hd
        omega
      exact ⟨hd, hs⟩
  | succ t ih =>
      by_cases hd : s.phase = .done
      · simpa only [run_done D s hd (t + 1)] using And.intro hd hs
      · have hnext := step_invariant hD hs
        have hlt := rank_step_lt (D := D) hs hd
        have hdone := ih hnext (by omega)
        simpa only [run] using hdone

theorem run_invariant {D : List Bool → Bool} (hD : DecidesExtension D)
    {r : RawInstance} {hr : r.Valid} {s : State} (hs : Invariant r hr s) (t : Nat) :
    Invariant r hr (run D t s) := by
  induction t generalizing s with
  | zero => exact hs
  | succ t ih => exact ih (step_invariant hD hs)

theorem search_optimal {D : List Bool → Bool} (hD : DecidesExtension D)
    (r : RawInstance) (hr : r.Valid) :
    ∃ p : RawPacking, search D r true = some p ∧
      p.Feasible r ∧ p.bins = opt (r.toInstance hr) := by
  let s := run D (fuel r) (initial r true)
  have hfinal := run_finishes hD (initial_invariant r hr) (fuel r) (rank_initial_le r)
  have hd : s.phase = .done := hfinal.1
  have hinv : DoneInvariant r hr s := by
    have hi := hfinal.2.2
    simpa only [show run D (fuel r) (initial r true) = s from rfl, hd] using hi
  refine ⟨⟨s.bins, labels s.fixed⟩, ?_, ?_, hinv.bins_eq⟩
  · change output s = some _
    simp [output, hd]
  · exact ext_complete hinv.extends (by simpa [hinv.fixed_length] using hinv.prefix)

@[simp] theorem search_empty (D : List Bool → Bool) :
    search D [] true = some ⟨0, []⟩ := by
  simp [search, initial, fuel, run, output, labels]

@[simp] theorem search_invalid (D : List Bool → Bool) (r : RawInstance) :
    search D r false = none := by
  simp [search, initial, run, output]

theorem fuel_eq_query_bound (r : RawInstance) :
    fuel r = r.length + r.length * r.length := by
  simp [fuel, Nat.mul_add, Nat.add_comm]

theorem fuel_empty : fuel [] = 0 := rfl

theorem search_query_count (D : List Bool → Bool) (r : RawInstance) :
    (queryTrace D (fuel r) (initial r true)).length =
      r.length + r.length * r.length := by
  rw [queryTrace_length, fuel_eq_query_bound]

end BinPackingGap.SearchSemantics

namespace BinPackingGap.ExtensionCertificate

open ExtensionQuery

def validItems (items : RawInstance) : Bool :=
  items.all fun q => decide (0 < q.1 ∧ q.1 ≤ q.2)

def agreesBool : List (Option Nat) → List Nat → Bool
  | [], [] => true
  | none :: fixed, _ :: assignments => agreesBool fixed assignments
  | some label :: fixed, value :: assignments =>
      decide (label = value) && agreesBool fixed assignments
  | _, _ => false

def capacityCheck (items : RawInstance) (assignments : List Nat) (label : Nat) : Bool :=
  let total := RawPacking.loadFraction items assignments label
  decide (total.1 ≤ total.2)

def check (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Bool :=
  validItems items &&
    (decide (assignments.length = items.length) &&
      (assignments.all (fun label => decide (label < bins)) &&
        (agreesBool fixed assignments &&
          assignments.all (capacityCheck items assignments))))

def verify (inputWitness : List Bool × List Bool) : Bool :=
  match BinaryEncoding.decodeExtension inputWitness.1,
      BinaryEncoding.decodeAssignments inputWitness.2 with
  | some (bins, items, fixed), some assignments => check bins items fixed assignments
  | _, _ => false

def language (input : List Bool) : Prop :=
  match BinaryEncoding.decodeExtension input with
  | some (bins, items, fixed) => Ext bins items fixed
  | none => False

@[simp] theorem validItems_eq_true_iff (items : RawInstance) :
    validItems items = true ↔ items.Valid := by
  simp [validItems, RawInstance.Valid]

@[simp] theorem agreesBool_eq_true_iff (fixed : List (Option Nat))
    (assignments : List Nat) : agreesBool fixed assignments = true ↔ Agrees fixed assignments := by
  induction fixed generalizing assignments with
  | nil => cases assignments <;> simp [agreesBool]
  | cons entry fixed ih =>
      cases assignments with
      | nil => simp [agreesBool]
      | cons value assignments =>
          cases entry <;> simp [agreesBool, agrees_cons, ih]

@[simp] theorem capacityCheck_eq_true_iff (items : RawInstance)
    (assignments : List Nat) (label : Nat) :
    capacityCheck items assignments label = true ↔
      (RawPacking.loadFraction items assignments label).1 ≤
        (RawPacking.loadFraction items assignments label).2 := by
  simp [capacityCheck]

theorem capacityCheck_eq_true_iff_load (items : RawInstance) (valid : items.Valid)
    (assignments : List Nat) (label : Nat) :
    capacityCheck items assignments label = true ↔
      RawPacking.load items assignments label ≤ 1 := by
  rw [capacityCheck_eq_true_iff]
  exact (RawPacking.load_le_one_iff items valid assignments label).symm

theorem check_eq_true_iff (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) :
    check bins items fixed assignments = true ↔
      items.Valid ∧ (RawPacking.mk bins assignments).Feasible items ∧
        Agrees fixed assignments := by
  simp only [check, Bool.and_eq_true, validItems_eq_true_iff,
    List.all_eq_true, decide_eq_true_eq, agreesBool_eq_true_iff,
    capacityCheck_eq_true_iff]
  constructor
  · rintro ⟨valid, lengths, range, agrees, capacities⟩
    refine ⟨valid, ?_, agrees⟩
    apply (RawPacking.feasible_iff_mem_capacity items ⟨bins, assignments⟩).mpr
    refine ⟨lengths, range, ?_⟩
    intro label mem
    exact (RawPacking.load_le_one_iff items valid assignments label).mpr
      (capacities label mem)
  · rintro ⟨valid, feasible, agrees⟩
    obtain ⟨lengths, range, capacities⟩ :=
      (RawPacking.feasible_iff_mem_capacity items ⟨bins, assignments⟩).mp feasible
    refine ⟨valid, lengths, range, agrees, ?_⟩
    intro label mem
    exact (RawPacking.load_le_one_iff items valid assignments label).mp
      (capacities label mem)

@[simp] theorem verify_encoded (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) :
    verify (BinaryEncoding.extensionBits bins items fixed,
      BinaryEncoding.assignmentBits assignments) = check bins items fixed assignments := by
  simp [verify]

@[simp] theorem language_extensionBits (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    language (BinaryEncoding.extensionBits bins items fixed) ↔ Ext bins items fixed := by
  simp [language]

theorem verify_sound (input witness : List Bool) (accepted : verify (input, witness) = true) :
    language input := by
  cases parsed : BinaryEncoding.decodeExtension input with
  | none => simp [verify, parsed] at accepted
  | some query =>
      rcases query with ⟨bins, items, fixed⟩
      cases certificate : BinaryEncoding.decodeAssignments witness with
      | none => simp [verify, parsed, certificate] at accepted
      | some assignments =>
          have checked : check bins items fixed assignments = true := by
            simpa [verify, parsed, certificate] using accepted
          obtain ⟨valid, feasible, agrees⟩ :=
            (check_eq_true_iff bins items fixed assignments).mp checked
          change (match BinaryEncoding.decodeExtension input with
            | some (b, r, p) => Ext b r p
            | none => False)
          rw [parsed]
          exact ⟨valid, assignments, feasible, agrees⟩

theorem verify_complete (input : List Bool) (member : language input) :
    ∃ assignments : List Nat, verify (input, BinaryEncoding.assignmentBits assignments) = true := by
  cases parsed : BinaryEncoding.decodeExtension input with
  | none => simp [language, parsed] at member
  | some query =>
      rcases query with ⟨bins, items, fixed⟩
      have extension : Ext bins items fixed := by simpa [language, parsed] using member
      obtain ⟨valid, assignments, feasible, agrees⟩ := extension
      refine ⟨assignments, ?_⟩
      have checked := (check_eq_true_iff bins items fixed assignments).mpr
        ⟨valid, feasible, agrees⟩
      simpa [verify, parsed] using checked

end BinPackingGap.ExtensionCertificate

namespace BinPackingGap.SearchEncoding

open SearchSemantics BinaryEncoding BinPackingGames.Foundations.Complexity

def phaseBits : Phase → List Bool
  | .find => [false, false]
  | .fill => [false, true]
  | .done => [true, false]
  | .invalid => [true, true]

def parsePhase : Parser Phase
  | false :: false :: rest => some (.find, rest)
  | false :: true :: rest => some (.fill, rest)
  | true :: false :: rest => some (.done, rest)
  | true :: true :: rest => some (.invalid, rest)
  | _ => none

@[simp] theorem phaseBits_length (phase : Phase) : (phaseBits phase).length = 2 := by
  cases phase <;> rfl

@[simp] theorem parsePhase_phaseBits (phase : Phase) (suffix : List Bool) :
    parsePhase (phaseBits phase ++ suffix) = some (phase, suffix) := by
  cases phase <;> rfl

def parseUnary : Parser Nat
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, rest) ← parseUnary rest
      return (n + 1, rest)

@[simp] theorem parseUnary_encodeWord (n : Nat) (suffix : List Bool) :
    parseUnary (encodeWord n ++ suffix) = some (n, suffix) := by
  induction n with
  | zero => simp [encodeWord, parseUnary]
  | succ n ih =>
    have word : encodeWord (n + 1) = true :: encodeWord n := by
      simp [encodeWord, List.replicate_succ]
    rw [word]
    simp [parseUnary, ih]

def fixedBits (fixed : List (Option Nat)) : List Bool :=
  listBits (optionBits natBits) fixed

def parseFixed : Parser (List (Option Nat)) := parseList (parseOption parseNat)

@[simp] theorem parseFixed_fixedBits (fixed : List (Option Nat)) (suffix : List Bool) :
    parseFixed (fixedBits fixed ++ suffix) = some (fixed, suffix) :=
  parseList_listBits (optionBits natBits) (parseOption parseNat)
    (parseOption_optionBits _ _ parseNat_natBits) fixed suffix

def stateBits (s : State) : List Bool :=
  phaseBits s.phase ++ encodeWord s.bins ++ encodeWord s.item ++ encodeWord s.label ++
    rawInstanceBits s.items ++ fixedBits s.fixed

def parseState (bits : List Bool) : Option (State × List Bool) := do
  let (phase, bits) ← parsePhase bits
  let (bins, bits) ← parseUnary bits
  let (item, bits) ← parseUnary bits
  let (label, bits) ← parseUnary bits
  let (items, bits) ← parseRawInstance bits
  let (fixed, bits) ← parseFixed bits
  return (⟨items, phase, bins, item, label, fixed⟩, bits)

def decodeState : List Bool → Option State := decode parseState

@[simp] theorem parseState_stateBits (s : State) (suffix : List Bool) :
    parseState (stateBits s ++ suffix) = some (s, suffix) := by
  cases s
  simp [parseState, stateBits, List.append_assoc]

@[simp] theorem decodeState_stateBits (s : State) : decodeState (stateBits s) = some s :=
  decode_encode _ _ parseState_stateBits s

theorem stateBits_injective : Function.Injective stateBits :=
  encode_injective _ _ parseState_stateBits

@[simp] theorem stateBits_length (s : State) :
    (stateBits s).length = 5 + s.bins + s.item + s.label +
      (rawInstanceBits s.items).length + (fixedBits s.fixed).length := by
  simp only [stateBits, List.length_append, phaseBits_length, encodeWord_length]
  omega

theorem label_le_stateBits_length (s : State) : s.label ≤ (stateBits s).length := by
  rw [stateBits_length]
  omega

private theorem size_le_self (n : Nat) : n.size ≤ n := by
  apply Nat.size_le.mpr
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem listBits_set_length_le {α : Type} (encode : α → List Bool)
    (xs : List α) (i : Nat) (x : α) :
    (listBits encode (xs.set i x)).length ≤
      (listBits encode xs).length + (encode x).length := by
  induction xs generalizing i with
  | nil => simp [listBits]
  | cons head tail ih =>
    cases i with
    | zero => simp [listBits]; omega
    | succ i =>
      have bound := ih i
      simp only [List.set_cons_succ, listBits, List.length_cons, List.length_append]
      omega

theorem fixedBits_set_length_le (fixed : List (Option Nat)) (i j : Nat) :
    (fixedBits (fixed.set i (some j))).length ≤
      (fixedBits fixed).length + 2 * j + 2 := by
  have bound := listBits_set_length_le (optionBits natBits) fixed i (some j)
  have width := size_le_self j
  simp only [optionBits, List.length_cons, natBits_length] at bound
  change (listBits (optionBits natBits) (fixed.set i (some j))).length ≤
    (listBits (optionBits natBits) fixed).length + 2 * j + 2
  omega

theorem update_label_le (s : State) (answer : Bool) :
    (update s answer).label ≤ s.label + 1 := by
  cases h : s.phase <;> cases answer <;> simp [update, h]

theorem update_length_le (s : State) (answer : Bool) :
    (stateBits (update s answer)).length ≤ (stateBits s).length + 2 * s.label + 5 := by
  have fixedBound := fixedBits_set_length_le s.fixed s.item s.label
  simp only [stateBits_length]
  cases h : s.phase <;> cases answer <;> simp [update, h] <;> omega

theorem step_label_le (D : List Bool → Bool) (s : State) :
    (step D s).label ≤ s.label + 1 := update_label_le s _

theorem step_length_le (D : List Bool → Bool) (s : State) :
    (stateBits (step D s)).length ≤ (stateBits s).length + 2 * s.label + 5 :=
  update_length_le s _

theorem iterate_label_le (D : List Bool → Bool) (s : State) (t : Nat) :
    ((step D)^[t] s).label ≤ s.label + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have bound := step_label_le D ((step D)^[t] s)
    omega

theorem iterate_length_le (D : List Bool → Bool) (s : State) (t : Nat) :
    (stateBits ((step D)^[t] s)).length ≤
      (stateBits s).length + t * (2 * s.label + 2 * t + 5) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have bound := step_length_le D ((step D)^[t] s)
    have labelBound := iterate_label_le D s t
    nlinarith

noncomputable def growthPolynomial : Polynomial Nat :=
  Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X + 1

theorem growthBound (D : List Bool → Bool) :
    MachineBoundedIteration.GrowthBound stateBits (step D) growthPolynomial := by
  intro p i hi
  let L := (MachineBoundedIteration.inputBits stateBits p).length
  have startBound : (stateBits p.2).length ≤ L := by
    dsimp [L]
    rw [MachineBoundedIteration.inputBits_length]
    omega
  have countBound : p.1 ≤ L := by
    dsimp [L]
    rw [MachineBoundedIteration.inputBits_length]
    omega
  have iBound : i ≤ L := hi.trans countBound
  have labelBound : p.2.label ≤ L := (label_le_stateBits_length p.2).trans startBound
  have coefficientBound : 2 * p.2.label + 2 * i + 5 ≤ 4 * L + 5 := by omega
  have productBound := Nat.mul_le_mul iBound coefficientBound
  have lengthBound := iterate_length_le D p.2 i
  change (stateBits ((step D)^[i] p.2)).length ≤ growthPolynomial.eval L
  simp only [growthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

end BinPackingGap.SearchEncoding

namespace BinPackingGap.SearchMachineComposition

open Turing BinPackingGames.Foundations.Complexity
open SearchSemantics SearchEncoding

def prepare (s : State) : State × List Bool := (s, query s)

def applyAnswer (p : State × Bool) : State := update p.1 p.2

def «initialize» (input : List Bool) : Nat × State :=
  match BinaryEncoding.decodeRawInstance input with
  | none => (0, initial [] false)
  | some items =>
      let valid := ExtensionCertificate.validItems items
      (if valid then fuel items else 0, initial items valid)

def algorithm (D : List Bool → Bool) (input : List Bool) : Option RawPacking :=
  output (MachineBoundedIteration.iterate (step D) («initialize» input))

theorem algorithm_eq_search (D : List Bool → Bool) (input : List Bool) :
    algorithm D input =
      match BinaryEncoding.decodeRawInstance input with
      | none => none
      | some items => search D items (ExtensionCertificate.validItems items) := by
  cases parsed : BinaryEncoding.decodeRawInstance input with
  | none => simp [algorithm, «initialize», parsed, MachineBoundedIteration.iterate,
      initial, output]
  | some items =>
      simp only [algorithm, «initialize», parsed, MachineBoundedIteration.iterate,
        search, run_eq_iterate]

@[simp] theorem algorithm_encoded (D : List Bool → Bool) (items : RawInstance) :
    algorithm D (BinaryEncoding.rawInstanceBits items) =
      search D items (ExtensionCertificate.validItems items) := by
  simp [algorithm_eq_search]

@[simp] theorem algorithm_malformed (D : List Bool → Bool) (input : List Bool)
    (malformed : BinaryEncoding.decodeRawInstance input = none) :
    algorithm D input = none := by
  simp [algorithm_eq_search, malformed]

theorem algorithm_invalid (D : List Bool → Bool) (items : RawInstance)
    (invalid : ¬ items.Valid) :
    algorithm D (BinaryEncoding.rawInstanceBits items) = none := by
  have rejected : ExtensionCertificate.validItems items = false := by
    cases checked : ExtensionCertificate.validItems items with
    | false => rfl
    | true => exact False.elim (invalid
        ((ExtensionCertificate.validItems_eq_true_iff items).mp checked))
  simp [rejected]

@[simp] theorem algorithm_empty (D : List Bool → Bool) :
    algorithm D (BinaryEncoding.rawInstanceBits []) = some ⟨0, []⟩ := by
  simp [ExtensionCertificate.validItems]

theorem algorithm_optimal {D : List Bool → Bool} (correct : DecidesExtension D)
    (items : RawInstance) (valid : items.Valid) :
    ∃ packing : RawPacking,
      algorithm D (BinaryEncoding.rawInstanceBits items) = some packing ∧
      packing.Feasible items ∧ packing.bins = opt (items.toInstance valid) := by
  have accepted : ExtensionCertificate.validItems items = true :=
    (ExtensionCertificate.validItems_eq_true_iff items).mpr valid
  simpa only [algorithm_encoded, accepted] using search_optimal correct items valid

structure Stages where
  initializeComputation : TM2ComputableInPolyTime (id : List Bool → List Bool)
    (MachineBoundedIteration.inputBits stateBits) «initialize»
  initializeFinite : MachineFiniteAlphabet.FiniteAlphabet initializeComputation.tm
  prepareComputation : TM2ComputableInPolyTime stateBits
    (MachineKeepDecision.typedInputBits stateBits) prepare
  prepareFinite : MachineFiniteAlphabet.FiniteAlphabet prepareComputation.tm
  updateComputation : TM2ComputableInPolyTime
    (MachineKeepDecision.typedOutputBits stateBits) stateBits applyAnswer
  updateFinite : MachineFiniteAlphabet.FiniteAlphabet updateComputation.tm
  finalizeComputation : TM2ComputableInPolyTime stateBits
    BinaryEncoding.packingResultBits output
  finalizeFinite : MachineFiniteAlphabet.FiniteAlphabet finalizeComputation.tm

noncomputable def bodyComputation (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D) :
    TM2ComputableInPolyTime stateBits stateBits (step D) :=
  MachineSequential.composeBits (f := prepare)
    (g := fun p => applyAnswer (MachineKeepDecision.typedKeep D p))
    stages.prepareComputation
    (MachineSequential.composeBits (f := MachineKeepDecision.typedKeep D) (g := applyAnswer)
      (MachineKeepDecision.computationWithSavedCodec stateBits D decision)
      stages.updateComputation)

theorem bodyComputation_finiteAlphabet (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (bodyComputation stages D decision).tm := by
  exact MachineFiniteAlphabet.composeBits stages.prepareComputation _
    stages.prepareFinite (MachineFiniteAlphabet.composeBits _ stages.updateComputation
      (MachineKeepDecision.computationWithSavedCodec_finiteAlphabet
        stateBits D decision finite) stages.updateFinite)

noncomputable def loopComputation (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D) :
    TM2ComputableInPolyTime (MachineBoundedIteration.inputBits stateBits) stateBits
      (MachineBoundedIteration.iterate (step D)) :=
  MachineBoundedIteration.computation stateBits (step D)
    (bodyComputation stages D decision) growthPolynomial (growthBound D)

theorem loopComputation_finiteAlphabet (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (loopComputation stages D decision).tm :=
  MachineBoundedIteration.computation_finiteAlphabet stateBits (step D)
    (bodyComputation stages D decision) growthPolynomial (growthBound D)
    (bodyComputation_finiteAlphabet stages D decision finite)

noncomputable def computation (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D) :
    TM2ComputableInPolyTime (id : List Bool → List Bool)
      BinaryEncoding.packingResultBits (algorithm D) :=
  MachineSequential.composeBits (f := «initialize»)
    (g := fun p => output (MachineBoundedIteration.iterate (step D) p))
    stages.initializeComputation
    (MachineSequential.composeBits (f := MachineBoundedIteration.iterate (step D))
      (g := output) (loopComputation stages D decision) stages.finalizeComputation)

theorem computation_finiteAlphabet (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation stages D decision).tm := by
  exact MachineFiniteAlphabet.composeBits stages.initializeComputation _
    stages.initializeFinite (MachineFiniteAlphabet.composeBits _ stages.finalizeComputation
      (loopComputation_finiteAlphabet stages D decision finite) stages.finalizeFinite)

end BinPackingGap.SearchMachineComposition

namespace BinPackingGap.SearchOptimalConstruction

open Turing BinPackingGames.Foundations.Complexity

theorem decidesExtension_of_language {D : List Bool → Bool}
    (correct : ∀ input, ExtensionCertificate.language input ↔ D input = true) :
    SearchSemantics.DecidesExtension D := by
  intro bins items fixed
  exact (correct (BinaryEncoding.extensionBits bins items fixed)).symm.trans
    (ExtensionCertificate.language_extensionBits bins items fixed)

noncomputable def ofDecision (stages : SearchMachineComposition.Stages)
    (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm)
    (correct : SearchSemantics.DecidesExtension D) : AbsoluteAdditiveAlgorithm 0 where
  run := SearchMachineComposition.algorithm D
  computation := SearchMachineComposition.computation stages D decision
  finiteAlphabet := SearchMachineComposition.computation_finiteAlphabet
    stages D decision finite
  guarantee items valid := by
    obtain ⟨packing, returned, feasible, optimal⟩ :=
      SearchMachineComposition.algorithm_optimal correct items valid
    exact ⟨packing, returned, feasible, by simp [optimal]⟩

theorem exists_of_stages_and_membership (stages : SearchMachineComposition.Stages)
    (membership : CookLevin.InNP ExtensionCertificate.language)
    (classEquality : PEqualsNP) : Nonempty (AbsoluteAdditiveAlgorithm 0) := by
  obtain ⟨D, decision, finite, correct⟩ := classEquality.inP membership
  exact ⟨ofDecision stages D decision finite (decidesExtension_of_language correct)⟩

end BinPackingGap.SearchOptimalConstruction

namespace BinPackingGap.SearchInitializeEncoding

open BinPackingGames.Foundations.Complexity

abbrev Data := RawInstance × Bool

def shapeBits (input : List Bool) : List Bool :=
  (BinaryEncoding.decodeRawInstance input).isSome :: input

def classify (input : List Bool) : Data :=
  match BinaryEncoding.decodeRawInstance input with
  | none => ([], false)
  | some items => (items, ExtensionCertificate.validItems items)

def dataBits (data : Data) : List Bool :=
  data.2 :: (encodeWord data.1.length ++ BinaryEncoding.rawInstanceBits data.1)

def emit (data : Data) : Nat × SearchSemantics.State :=
  (if data.2 then SearchSemantics.fuel data.1 else 0,
    SearchSemantics.initial data.1 data.2)

theorem emit_classify (input : List Bool) :
    emit (classify input) = SearchMachineComposition.initialize input := by
  unfold classify SearchMachineComposition.initialize
  cases BinaryEncoding.decodeRawInstance input <;> rfl

end BinPackingGap.SearchInitializeEncoding

end OAI
