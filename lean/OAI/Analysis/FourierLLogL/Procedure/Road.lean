import OAI.Analysis.FourierLLogL.Procedure.Fork

/-! # The road seen from the input. This representation can truncate the play at transfers. -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork
variable {M J j : ℕ} {s : Scene M}
open scoped Classical

/-- Unary pace: entering the static system, or starting a new plateau -/
inductive Pace
| renew | cross deriving DecidableEq

def Scene.pace (s : Scene M) (v : Pace) :=
    match v with | .renew => s.reset | .cross => s.out

lemma pace_mass (s : Scene M) (v : Pace) : (s.pace v).mass=s.mass := by cases v <;> rfl
lemma pace_actor (s : Scene M) (v : Pace) : (s.pace v).actor=s.actor := by cases v <;> rfl

inductive Turn (j : ℕ) (s : Scene M) : Type
| ask (u : Update j M s.here) : Turn j s
| move : Turn j s

def Turn.fork (v : Turn j s) :=
    match v with | .ask u => toss s u | .move => step s

lemma Turn.source (v : Turn j s) : v.fork.src=s := by cases v <;> rfl

inductive Road (j M : ℕ) : Scene M → Type
| finish (s : Scene M) (transferred : Bool) : Road j M s
| push (s : Scene M) (v : Pace) (t : Road j M (s.pace v)) : Road j M s
| fork (s : Scene M) (v : Turn j s) (t : (b : Bool) → Road j M (v.fork.dst b)) : Road j M s

namespace Road

/-- `extend` means continuing into the static system. -/
def trace (throughCold : Bool) {s : Scene M} (t : Play j M s) : Road j M s :=
    match t with
    | .rest s => .finish s false
    | .freeze s t => if throughCold then .push s .cross (trace throughCold t) else .finish s true
    | .ticket s t => .push s .renew (trace throughCold t)
    | .jump s l r => .fork s .move fun b =>
        match b with | false => trace throughCold l | true => trace throughCold r
    | .attempt s u l r => .fork s (.ask u) fun b =>
        match b with | false => trace throughCold l | true => trace throughCold r

variable {f : Grid M → ℝ}

def pace_ok (s : Scene M) (v : Pace) (j : ℕ) :=
    match v with | .renew => ¬ s.retire j ∧ s.enter | .cross => s.retire j
def turn_ok {s : Scene M} (v : Turn j s) :=
    match v with
    | .ask u => s.live=true ∧ u.Good capA s.fund.mood s.actor
    | .move => s.settled j

/-- f and J ambient original data. -/
def Trusted (J : ℕ) (f : Grid M → ℝ) {s : Scene M} (r : Road j M s) : Prop :=
    match r with
    | .finish s b => s.Safe j J f ∧ (if b then s.openHere j J f ∧ s.retire j else ¬ s.openHere j J f)
    | .push s v t => s.Safe j J f ∧ s.openHere j J f ∧ pace_ok s v j ∧ Trusted J f t
    | .fork s v t => s.Safe j J f ∧ s.work j J f ∧ turn_ok v ∧ ∀ b, Trusted J f (t b)

lemma traced {s : Scene M} (t : Play j M s) (b : Bool) (h : t.Follows J f) :
    (trace b t).Trusted J f := by
  induction t with
  | rest s => exact ⟨h.1,h.2⟩
  | freeze s t ih =>
    obtain ⟨ha,hb,hc,hd⟩ := h
    cases b; exact ⟨ha,hb,hc⟩; exact ⟨ha,hb,hc,ih hd⟩
  | ticket s t ih =>
    obtain ⟨ha,hb,hc,hd,he⟩ := h
    exact ⟨ha,hb,⟨hc,hd⟩,ih he⟩
  | jump s l r il ir =>
    obtain ⟨ha,hb,hc,hd,he⟩ := h
    refine ⟨ha,hb,hc,?_⟩
    intro b; cases b; exact il hd; exact ir he
  | attempt s u l r il ir =>
    obtain ⟨ha,hb,hc,hd,he,hf⟩ := h
    refine ⟨ha,hb,⟨hc,hd⟩,?_⟩
    intro b; cases b; exact il he; exact ir hf

lemma rootSafe {t : Road j M s} (h : t.Trusted J f) : Safe s j J f := by
  cases t <;> exact h.1

lemma branchTrusted {v : Turn j s} {t : ∀ b, Road j M (v.fork.dst b)}
    (h : (Road.fork s v t).Trusted J f) : v.fork.TrueLaw := by
  obtain ⟨ha,hb,hc,hd⟩ := h
  cases v with
  | ask u => exact toss_true _ ha.within ha.positive hb.1.2.2
  | move =>
    have Hh := (rootSafe (hd false)).within.2
    exact step_true ha.within.1 Hh ha.positive hb.1.2.2

end Road

/-- One edge actually seen. -/
inductive Event (j M : ℕ)
| march (s : Scene M) (v : Turn j s) (b : Bool) : Event j M
| pace (s : Scene M) (v : Pace) : Event j M

def Event.dest (p : Event j M) : Scene M :=
    match p with | .pace s v => s.pace v | .march _ v b => v.fork.dst b
def Event.src (p : Event j M) : Scene M :=
    match p with | .pace s _ | .march s _ _ => s

structure Journal (j M : ℕ) where
  done : Scene M
  froze : Bool
  events : List (Event j M)

namespace Journal
def prepend (e : Event j M) (z : Journal j M) := {z with events:=e::z.events}
def fee (z : Journal j M) (f : Event j M → ℝ) := (z.events.map f).sum

lemma fee_pre (e : Event j M) (z : Journal j M) (f : Event j M → ℝ) :
    (z.prepend e).fee f = f e + z.fee f := by simp [prepend,fee]

end Journal

namespace Road
open Event Journal

def hike {s : Scene M} (t : Road j M s) (x : Grid M) : Journal j M :=
    match t with
    | .finish s b => ⟨s,b,[]⟩
    | .push s v t => (t.hike x).prepend (Event.pace s v)
    | .fork s v t =>
        let b := v.fork.bit x
        ((t b).hike x).prepend (Event.march s v b)

/-- True induction along the observed path. -/
lemma travel {f : Grid M → ℝ} {good : Scene M → Journal j M → Prop}
    (he : ∀ s b, Safe s j J f → (if b then s.openHere j J f ∧ s.retire j else ¬ s.openHere j J f) →
       0 < s.mass → good s ⟨s,b,[]⟩)
    (h1 : ∀ (s : Scene M) (v : Pace), Safe s j J f → s.openHere j J f → pace_ok s v j →
      ∀ l : Journal j M, good (s.pace v) l → good s (l.prepend (Event.pace s v)))
    (h2 : ∀ (s : Scene M) (v : Turn j s), Safe s j J f → s.work j J f → turn_ok v →
      v.fork.TrueLaw →
      ∀ b : Bool, 0 < v.fork.probs b → ∀ l, good (v.fork.dst b) l → good s (l.prepend (.march s v b)))
    (t : Road j M s) (h : t.Trusted J f) (hm : 0 < s.mass) {x : Grid M} (hx : 0 < s.actor x) :
    good s (t.hike x) := by
  induction t with
  | finish s b => exact he _ _ h.1 h.2 hm
  | push s v t ih =>
    obtain ⟨ha,hb,hc,hd⟩ := h
    exact h1 s v ha hb hc _ (ih hd (by rw [pace_mass]; exact hm) (by rw [pace_actor]; exact hx))
  | fork s v t ih =>
    have hf := branchTrusted h
    obtain ⟨hx1,hx2⟩ := Fork.branch_pos hf (x:=x) (by rw [Turn.source]; exact hx)
    obtain ⟨ha,hb,hc,hd⟩ := h
    exact h2 s v ha hb hc hf _ hx1 _ (ih _ (hd _) ((true_mass hf).mp hx1) hx2)

def expHike (t : Road j M s) (f : Journal j M → Grid M → ℝ) :=
    s.actor.Ex (fun x => f (hike t x) x)

lemma Ex_hike_fork {f : Grid M → ℝ} {v : Turn j s} {t : ∀ b, Road j M (v.fork.dst b)}
    (h : (Road.fork s v t).Trusted J f) (F : Journal j M → Grid M → ℝ) :
    expHike (Road.fork s v t) F = v.fork.probs.Ex (fun b =>
      expHike (t b) (fun l x => F (l.prepend (.march s v b)) x)) := by
  unfold expHike
  let g := fun (b : Bool) x => F ((hike (t b) x).prepend (.march s v b)) x
  have hi := expect_bit (branchTrusted h) g
  rw [Turn.source] at hi
  exact hi.symm

lemma Ex_hike_push {v : Pace} {t : Road j M (s.pace v)} (F : Journal j M → Grid M → ℝ) :
    expHike (.push s v t) F = expHike t (fun l x => F (l.prepend (.pace s v)) x) := by
  simp only [expHike,pace_actor,hike]

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
