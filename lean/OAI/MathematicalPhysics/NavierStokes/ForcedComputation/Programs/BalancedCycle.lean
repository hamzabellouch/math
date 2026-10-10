import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedRules

namespace OAI

/-! Finite sweeps in the balanced recorder.  The preparatory cycle restores
both work tapes and moves exactly one blank onto the history stack. -/

namespace ForcedComputation.Balanced

variable {Q A : Type*}
open ForcedComputation.Balanced.Symbol

abbrev push := @Radix.prepend (Symbol Q A)
abbrev word := @Radix.prependWord (Symbol Q A)

def triple (q : Control Q) (l r h : Stack Q A) : Configuration Q A :=
  ⟨q, ![l, r, h]⟩

theorem prefixConfiguration_three (q : Control Q)
    (a b c : List (Symbol Q A)) (l r h : Stack Q A) :
    prefixConfiguration q ![a, b, c] ![l, r, h] =
      triple q (word a l) (word b r) (word c h) := by
  change Configuration.mk q _ = Configuration.mk q _
  apply congrArg (Configuration.mk q)
  funext j
  fin_cases j <;> rfl

inductive Steps (M : Recorder.Machine Q A) (blank : A) :
    ℕ → Configuration Q A → Configuration Q A → Prop
  | refl (x) : Steps M blank 0 x x
  | next {n x y z} : Step M blank x y → Steps M blank n y z → Steps M blank (n + 1) x z

theorem Step.steps {M : Recorder.Machine Q A} {blank : A} {x y : Configuration Q A}
    (h : Step M blank x y) : Steps M blank 1 x y :=
  .next h (.refl y)

theorem Steps.trans {M : Recorder.Machine Q A} {blank : A}
    {n m : ℕ} {x y z : Configuration Q A}
    (hxy : Steps M blank n x y) (hyz : Steps M blank m y z) : Steps M blank (n + m) x z := by
  induction hxy with
  | refl => simpa only [Nat.zero_add] using hyz
  | next hxy hrest ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using Steps.next hxy (ih hyz)

theorem enter_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (a : A)
    (hq : M.halting q = false) (l r h : Stack Q A) :
    Step M blank (triple (.checkpoint q) l (push (work a) r) h)
      (triple (.outward q) (push (marked a) l) r h) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.enter q a).step hq ![l, r, h]

theorem outward_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (c : A)
    (l r h : Stack Q A) :
    Step M blank (triple (.outward q) l (push (work c) r) h)
      (triple (.outward q) (push (work c) l) r h) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.outward q c).step (M := M) (blank := blank) trivial ![l, r, h]

theorem supply_step (M : Recorder.Machine Q A) (blank : A) (q : Q)
    (l r h : Stack Q A) :
    Step M blank (triple (.outward q) l (push .boundary (push (work blank) r)) h)
      (triple (.inward q) l (push .boundary r) (push (work blank) h)) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.supply q).step (M := M) (blank := blank) trivial ![l, r, h]

theorem inward_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (c : A)
    (l r h : Stack Q A) :
    Step M blank (triple (.inward q) (push (work c) l) r h)
      (triple (.inward q) l (push (work c) r) h) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.inward q c).step (M := M) (blank := blank) trivial ![l, r, h]

theorem restore_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (a : A)
    (l r h : Stack Q A) :
    Step M blank (triple (.inward q) (push (marked a) l) r h)
      (triple (.dispatch q) l (push (work a) r) h) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.restore q a).step (M := M) (blank := blank) trivial ![l, r, h]

theorem word_append (a b : List (Symbol Q A)) (u : Stack Q A) :
    word (a ++ b) u = word a (word b u) := by
  induction a with
  | nil => rfl
  | cons c a ih => simp only [List.cons_append, Radix.prependWord, ih]

abbrev workWord (w : List A) : List (Symbol Q A) := w.map work

theorem outward_sweep (M : Recorder.Machine Q A) (blank : A) (q : Q)
    (w : List A) (l r h : Stack Q A) :
    Steps M blank w.length (triple (.outward q) l (word (workWord w) r) h)
      (triple (.outward q) (word (workWord w.reverse) l) r h) := by
  induction w generalizing l with
  | nil => exact .refl _
  | cons c w ih =>
    have hh := Steps.next (outward_step M blank q c l (word (workWord w) r) h)
      (ih (push (work c) l))
    simpa only [List.length_cons, workWord, List.map_cons, List.reverse_cons,
      List.map_append, List.map_singleton, List.map_nil, word_append, Radix.prependWord] using hh

theorem inward_sweep (M : Recorder.Machine Q A) (blank : A) (q : Q)
    (w : List A) (l r h : Stack Q A) :
    Steps M blank w.length (triple (.inward q) (word (workWord w) l) r h)
      (triple (.inward q) l (word (workWord w.reverse) r) h) := by
  induction w generalizing r with
  | nil => exact .refl _
  | cons c w ih =>
    have hh := Steps.next (inward_step M blank q c (word (workWord w) l) r h)
      (ih (push (work c) r))
    simpa only [List.length_cons, workWord, List.map_cons, List.reverse_cons,
      List.map_append, List.map_singleton, List.map_nil, word_append, Radix.prependWord] using hh

/-- On arbitrary independent tails, preparation removes one right-tail blank
and adds that same blank to history, leaving the finite work window unchanged. -/
theorem preparation (M : Recorder.Machine Q A) (blank : A) (q : Q) (a : A)
    (hq : M.halting q = false) (w : List A) (l r h : Stack Q A) :
    Steps M blank (2 * w.length + 3)
      (triple (.checkpoint q) l
        (push (work a) (word (workWord w) (push .boundary (push (work blank) r)))) h)
      (triple (.dispatch q) l
        (push (work a) (word (workWord w) (push .boundary r))) (push (work blank) h)) := by
  have h₁ := (enter_step M blank q a hq l
    (word (workWord w) (push .boundary (push (work blank) r))) h).steps
  have h₂ := outward_sweep M blank q w (push (marked a) l)
    (push .boundary (push (work blank) r)) h
  have h₃ := (supply_step M blank q (word (workWord w.reverse) (push (marked a) l)) r h).steps
  have h₄ := inward_sweep M blank q w.reverse (push (marked a) l)
    (push .boundary r) (push (work blank) h)
  have h₅ := (restore_step M blank q a l (word (workWord w) (push .boundary r))
    (push (work blank) h)).steps
  simp only [List.reverse_reverse, List.length_reverse] at h₄
  have hh := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  convert hh using 1
  omega

theorem stay_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (a : A)
    (hm : M.move q a = 0) (l r h : Stack Q A) :
    Step M blank (triple (.dispatch q) l (push (work a) r) (push (work blank) h))
      (triple (.checkpoint (M.next q a)) l (push (work (M.write q a)) r)
        (push (record (.stay q a)) h)) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.stay q a).step hm ![l, r, h]

theorem left_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (a c : A)
    (hm : M.move q a = -1) (l r h : Stack Q A) :
    Step M blank
      (triple (.dispatch q) (push (work c) l) (push (work a) r) (push (work blank) h))
      (triple (.checkpoint (M.next q a)) l (push (work c) (push (work (M.write q a)) r))
        (push (record (.left q a c)) h)) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.left q a c).step hm ![l, r, h]

theorem right_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (a c : A)
    (hm : M.move q a = 1) (l r h : Stack Q A) :
    Step M blank
      (triple (.dispatch q) l (push (work a) (push (work c) r)) (push (work blank) h))
      (triple (.checkpoint (M.next q a)) (push (work (M.write q a)) l) (push (work c) r)
        (push (record (.right q a c)) h)) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.right q a c).step hm ![l, r, h]

theorem boundary_step (M : Recorder.Machine Q A) (blank : A) (q : Q) (a : A)
    (hm : M.move q a = 1) (l r h : Stack Q A) :
    Step M blank (triple (.dispatch q) l
      (push (work a) (push .boundary (push (work blank) r))) (push (work blank) h))
      (triple (.checkpoint (M.next q a)) (push (work (M.write q a)) l)
        (push (work blank) (push .boundary r)) (push (record (.boundary q a)) h)) := by
  simpa only [Row.source, Row.target, Row.sourceControl, Row.targetControl,
    Row.sourcePrefixes, Row.targetPrefixes, prefixConfiguration_three,
    Radix.prependWord] using (Row.boundary q a).step hm ![l, r, h]

theorem stay_cycle (M : Recorder.Machine Q A) (blank : A) (q : Q) (a : A)
    (hq : M.halting q = false) (hm : M.move q a = 0) (w : List A) (l r h : Stack Q A) :
    Steps M blank (2 * (w.length + 1) + 2)
      (triple (.checkpoint q) l
        (push (work a) (word (workWord w) (push .boundary (push (work blank) r)))) h)
      (triple (.checkpoint (M.next q a)) l
        (push (work (M.write q a)) (word (workWord w) (push .boundary r)))
        (push (record (.stay q a)) h)) := by
  have hp := preparation M blank q a hq w l r h
  have hh := hp.trans (stay_step M blank q a hm l (word (workWord w) (push .boundary r)) h).steps
  convert hh using 1

theorem left_cycle (M : Recorder.Machine Q A) (blank : A) (q : Q) (a c : A)
    (hq : M.halting q = false) (hm : M.move q a = -1) (w : List A) (l r h : Stack Q A) :
    Steps M blank (2 * (w.length + 1) + 2)
      (triple (.checkpoint q) (push (work c) l)
        (push (work a) (word (workWord w) (push .boundary (push (work blank) r)))) h)
      (triple (.checkpoint (M.next q a)) l
        (push (work c) (push (work (M.write q a)) (word (workWord w) (push .boundary r))))
        (push (record (.left q a c)) h)) := by
  have hp := preparation M blank q a hq w (push (work c) l) r h
  have hh := hp.trans (left_step M blank q a c hm l (word (workWord w) (push .boundary r)) h).steps
  convert hh using 1

theorem right_cycle (M : Recorder.Machine Q A) (blank : A) (q : Q) (a c : A)
    (hq : M.halting q = false) (hm : M.move q a = 1) (w : List A) (l r h : Stack Q A) :
    Steps M blank (2 * (w.length + 2) + 2)
      (triple (.checkpoint q) l
        (push (work a) (push (work c)
          (word (workWord w) (push .boundary (push (work blank) r))))) h)
      (triple (.checkpoint (M.next q a)) (push (work (M.write q a)) l)
        (push (work c) (word (workWord w) (push .boundary r)))
        (push (record (.right q a c)) h)) := by
  have hp := preparation M blank q a hq (c :: w) l r h
  simp only [workWord, List.map_cons, Radix.prependWord] at hp
  have hh := hp.trans (right_step M blank q a c hm l
    (word (workWord w) (push .boundary r)) h).steps
  convert hh using 1

/-- A right move at the boundary creates a new blank work cell while retaining
one boundary and the same infinite blank filler. -/
theorem boundary_cycle (M : Recorder.Machine Q A) (blank : A) (q : Q) (a : A)
    (hq : M.halting q = false) (hm : M.move q a = 1) (l h : Stack Q A) :
    Steps M blank 4
      (triple (.checkpoint q) l
        (push (work a) (push .boundary (fun _ => work blank))) h)
      (triple (.checkpoint (M.next q a)) (push (work (M.write q a)) l)
        (push (work blank) (push .boundary (fun _ => work blank)))
        (push (record (.boundary q a)) h)) := by
  have hz : push (work blank) (fun _ : ℕ => work blank : Stack Q A) =
      (fun _ => work blank) := by
    funext n
    cases n <;> rfl
  have hp := preparation M blank q a hq [] l (fun _ => work blank) h
  simp only [workWord, List.map_nil, Radix.prependWord, List.length_nil,
    Nat.mul_zero, Nat.zero_add, hz] at hp
  have ht := boundary_step M blank q a hm l (fun _ => work blank) h
  rw [hz] at ht
  simpa only [Nat.reduceAdd] using hp.trans ht.steps

end ForcedComputation.Balanced

end OAI
