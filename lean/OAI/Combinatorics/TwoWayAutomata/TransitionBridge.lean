import OAI.Combinatorics.TwoWayAutomata.DeterministicCore
import OAI.Combinatorics.TwoWayAutomata.Normalization
import OAI.Combinatorics.Automata.Model

namespace OAI

namespace TwoWayComplementation.CompanionBridge

open OneWayLiveness

/-- The encodings have the same two distinct endmarkers. -/
def encodeSymbol {Alpha : Type*} : Symbol Alpha → Fin 2 ⊕ Alpha
  | .left => .inl 0
  | .letter a => .inr a
  | .right => .inl 1

theorem encode_scanned {Alpha : Type*} (w : List Alpha) (p : Fin (w.length + 2)) :
    encodeSymbol (scanned w p) = tapeSymbol w p := by
  unfold scanned tapeSymbol
  split_ifs <;> simp_all [encodeSymbol] <;> omega

def encodeMove : Move → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

def decodeMove (m : Fin 3) : Move :=
  if m = 0 then .left else if m = 1 then .stay else .right

@[simp] theorem encode_decode (m : Fin 3) : encodeMove (decodeMove m) = m := by
  fin_cases m <;> rfl

theorem encodeMove_injective : Function.Injective encodeMove := by
  intro a b h
  cases a <;> cases b <;> simp_all [encodeMove]

theorem move_rel_iff (m : Move) (i j : ℕ) :
    m.Rel i j ↔ (j : ℤ) = (i : ℤ) + ((encodeMove m).val : ℤ) - 1 := by
  cases m <;> simp [Move.Rel, encodeMove] <;> omega

/-- A marker-outward transition is never usable on this bounded tape. -/
def Guard {Alpha : Type*} (a : Symbol Alpha) (m : Move) : Prop :=
  (a = .left → m ≠ .left) ∧ (a = .right → m ≠ .right)

theorem guard_of_legal_move {Alpha : Type*} (w : List Alpha)
    (p r : Fin (w.length + 2)) (m : Move) (h : m.Rel p.val r.val) :
    Guard (scanned w p) m := by
  constructor
  · intro hs hm
    subst m
    have hp : p.val = 0 := (tapeSymbol_left_iff w p).mp (by
      rw [← encode_scanned, hs]; rfl)
    simp only [Move.Rel] at h
    omega
  · intro hs hm
    subst m
    have hp : p.val = w.length + 1 := (tapeSymbol_right_iff w p).mp (by
      rw [← encode_scanned, hs]; rfl)
    simp only [Move.Rel] at h
    omega

/-- Option-valued form of a partial transition. Only the single allowed element is selected. -/
noncomputable def select {X : Type*} (S : Set X) : Option X := by
  classical
  exact if h : S.Nonempty then some h.choose else none

theorem select_eq_some_iff {X : Type*} (S : Set X) (hS : S.Subsingleton) (x : X) :
    select S = some x ↔ x ∈ S := by
  classical
  unfold select
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun hx => hx ▸ h.choose_spec, fun hx => hS h.choose_spec hx⟩
  · simp only [false_iff]
    exact fun hx => h ⟨x, hx⟩

/-- Recode moves and remove only impossible outward marker transitions. -/
def convertedTransitions {Alpha : Type*} {s : ℕ} (A : TwoNFA Alpha (Fin s))
    (q : Fin s) (a : Symbol Alpha) : Set (Fin s × Move) :=
  {t | (t.1, encodeMove t.2) ∈ A.transition q (encodeSymbol a) ∧ Guard a t.2}

theorem convertedTransitions_subsingleton {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) (q : Fin s) (a : Symbol Alpha) :
    (convertedTransitions A q a).Subsingleton := by
  intro x hx y hy
  have h := hA q (encodeSymbol a) hx.1 hy.1
  apply Prod.ext
  · exact congrArg (fun t : Fin s × Fin 3 => t.1) h
  · exact encodeMove_injective (congrArg (fun t : Fin s × Fin 3 => t.2) h)

/-- A deterministic machine with exactly the same states and finite accepting runs.
No halting or totality condition is introduced. -/
noncomputable def toDMachine {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) : DMachine Alpha s where
  initial := A.initial
  accepting := A.accepting
  transition q a := select (convertedTransitions A q a)
  left_boundary q q' he := by
    have h := (select_eq_some_iff _ (convertedTransitions_subsingleton A hA q .left) _).mp he
    exact h.2.1 rfl rfl
  right_boundary q q' he := by
    have h := (select_eq_some_iff _ (convertedTransitions_subsingleton A hA q .right) _).mp he
    exact h.2.2 rfl rfl

theorem toDMachine_step {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) (w : List Alpha)
    (c d : Fin s × Fin (w.length + 2)) :
    (toDMachine A hA).Step w (c.2, c.1) (d.2, d.1) ↔ (c, d) ∈ A.step w := by
  change (∃ m, select (convertedTransitions A c.1 (scanned w c.2)) = some (d.1, m) ∧
    m.Rel c.2.val d.2.val) ↔ _
  simp only [select_eq_some_iff _ (convertedTransitions_subsingleton A hA _ _)]
  constructor
  · rintro ⟨m, hm, hrel⟩
    refine ⟨encodeMove m, ?_, (move_rel_iff m _ _).mp hrel⟩
    simpa only [encode_scanned] using hm.1
  · rintro ⟨m, hm, hrel⟩
    have hr : (decodeMove m).Rel c.2.val d.2.val := by
      rw [move_rel_iff, encode_decode]
      exact hrel
    refine ⟨decodeMove m, ⟨?_, guard_of_legal_move w c.2 d.2 _ hr⟩, hr⟩
    simpa only [encode_decode, encode_scanned] using hm

theorem toDMachine_accepts {Alpha : Type*} {s : ℕ}
    (A : TwoNFA Alpha (Fin s)) (hA : A.Deterministic) (w : List Alpha) :
    (toDMachine A hA).Accepts false w ↔ w ∈ A.language := by
  constructor
  · rintro ⟨⟨p, q⟩, hr, hq⟩
    refine ⟨(q, p), hq, ?_⟩
    change Relation.ReflTransGen ((toDMachine A hA).Step w) _ _ at hr
    exact hr.lift (fun c => (c.2, c.1))
      (p := fun c d => (c, d) ∈ A.step w) (fun c d h =>
        (toDMachine_step A hA w (c.2, c.1) (d.2, d.1)).mp h)
  · rintro ⟨⟨q, p⟩, hq, hr⟩
    refine ⟨(p, q), ?_, hq⟩
    exact hr.lift (fun c => (c.2, c.1))
      (p := (toDMachine A hA).Step w) (fun c d h =>
        (toDMachine_step A hA w c d).mpr h)

end TwoWayComplementation.CompanionBridge

end OAI
