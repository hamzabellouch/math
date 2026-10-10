import OAI.Computability.SpaceSimulation.StackMachine

namespace OAI

/-! Sliding representation of a tape/configuration for emulating a
multi-work-tape program with stacks. -/
namespace Fifths

structure WorkSplit (A : Type) where
  center : A
  lo : List A
  hi : List A

namespace WorkSplit
variable {A : Type}

def init (b : A) : WorkSplit A := ⟨b, [], []⟩
/-- Full-tape agreement (padding by blank), plus inclusion of both
lists in the allowed tape window. -/
structure Good (z : WorkSplit A) (t : Tape A) (b : A) (l r : ℕ) : Prop where
  see : t.see = z.center
  down : ∀ n : ℕ, t.sym (t.pos - (n+1:ℕ)) = (z.lo[n]?).getD b
  up : ∀ n : ℕ, t.sym (t.pos + (n+1:ℕ)) = (z.hi[n]?).getD b
  lb : -(l:ℤ) ≤ t.pos - z.lo.length
  hb : t.pos + z.hi.length ≤ (r:ℤ)

theorem init_good (b : A) (l r) : (init b).Good (Tape.init b) b l r := by
  constructor
  · rfl
  · simp [Tape.init,init]
  · simp [Tape.init,init]
  · simp [Tape.init,init]
  · simp [Tape.init,init]

theorem good_lengths {z : WorkSplit A} {t b l r} (g : z.Good t b l r) :
    z.lo.length ≤ l+r ∧ z.hi.length ≤ l+r := by
  have a := g.lb
  have c := g.hb
  omega

def slide (z : WorkSplit A) (m : WriteMove A) (b : A) : WorkSplit A :=
  match m.dir with
  | .N => ⟨m.sym,z.lo,z.hi⟩
  | .R => ⟨z.hi.head?.getD b, m.sym :: z.lo, z.hi.tail⟩
  | .L => ⟨z.lo.head?.getD b, z.lo.tail, m.sym :: z.hi⟩

theorem good_slide {z : WorkSplit A} {t b l r} (m : WriteMove A)
    (g : z.Good t b l r)
    (hl : -(l:ℤ) ≤ (t.perform m).pos)
    (hr : (t.perform m).pos ≤ (r:ℤ)) :
    (z.slide m b).Good (t.perform m) b l r := by
  obtain ⟨s,d⟩ := m
  rcases g with ⟨e,a,c,u,v⟩
  cases d
  case N =>
    constructor
    · simp [slide,Tape.perform,Tape.see]
    · intro n
      simp only [Tape.perform,Dir.delta, add_zero, slide]
      rw [Function.update_of_ne (by omega)]
      exact a n
    · intro n
      simp only [Tape.perform,Dir.delta, add_zero, slide]
      rw [Function.update_of_ne (by omega)]
      exact c n
    · simpa [Tape.perform,slide] using u
    · simpa [Tape.perform,slide] using v
  case R =>
    constructor
    · simp only [slide,Tape.perform,Tape.see,Dir.delta]
      rw [Function.update_of_ne (by omega)]
      specialize c 0
      cases h : z.hi <;> simpa [h] using c
    · intro n; cases n with
      | zero => simp [Tape.perform,slide]
      | succ n =>
        simp only [Tape.perform,slide,Dir.delta,List.getElem?_cons_succ]
        rw [show t.pos + 1 - (((n+1+1:ℕ)):ℤ) = t.pos - (((n+1:ℕ)):ℤ) by omega,
          Function.update_of_ne (by omega)]
        exact a n
    · intro n
      simp only [Tape.perform,slide,Dir.delta]
      rw [show t.pos + 1 + (((n+1:ℕ)):ℤ) = t.pos + (((n+1+1:ℕ)):ℤ) by omega,
        Function.update_of_ne (by omega)]
      specialize c (n+1)
      cases h : z.hi <;> simpa [h] using c
    · simp only [Tape.perform, slide, Dir.delta, List.length_cons]
      omega
    · cases h : z.hi with
      | nil => simpa [Tape.perform,slide,h] using hr
      | cons a m =>
        simp only [Tape.perform,slide,Dir.delta,h,List.tail_cons]
        rw [h, List.length_cons] at v
        omega
  case L =>
    constructor
    · simp only [slide,Tape.perform,Tape.see,Dir.delta]
      rw [Function.update_of_ne (by omega)]
      specialize a 0
      cases h : z.lo <;> simpa [h,sub_eq_add_neg] using a
    · intro n
      simp only [Tape.perform,slide,Dir.delta]
      rw [show t.pos + -1 - (((n+1:ℕ)):ℤ) = t.pos - (((n+1+1:ℕ)):ℤ) by omega,
        Function.update_of_ne (by omega)]
      specialize a (n+1)
      cases h : z.lo <;> simpa [h] using a
    · intro n; cases n with
      | zero => simp [Tape.perform,slide]
      | succ n =>
        simp only [Tape.perform,slide,Dir.delta,List.getElem?_cons_succ]
        rw [show t.pos + -1 + (((n+1+1:ℕ)):ℤ) = t.pos + (((n+1:ℕ)):ℤ) by omega,
          Function.update_of_ne (by omega)]
        exact c n
    · cases h : z.lo with
      | nil => simpa [Tape.perform,slide,h] using hl
      | cons a m =>
        simp only [Tape.perform,slide,Dir.delta,h,List.tail_cons]
        rw [h, List.length_cons] at u
        omega
    · simp only [Tape.perform,slide,Dir.delta,List.length_cons]
      omega
end WorkSplit

/-- Unlike the work splits, never push either marker. -/
structure ArgSplit where
  center : Mark Bool
  lo : List Bool
  hi : List Bool

namespace ArgSplit
def init (w : List Bool) : ArgSplit := ⟨.left, [], w⟩

inductive Good : ArgSplit → List Bool → ℕ → Prop
  | left (h) : Good ⟨.left, [], h⟩ h 0
  | right (l : List Bool) : Good ⟨.right, l, []⟩ l.reverse (l.length+1)
  | sym (b l h) : Good ⟨.sym b, l, h⟩ (l.reverse ++ b::h) (l.length+1)

theorem good_see {z : ArgSplit} {w p} (g : z.Good w p) :
    Mark.see w p = z.center := by
  cases g with
  | left => rfl
  | right l =>
    simp [Mark.see]
  | sym b l h =>
    simp [Mark.see]

theorem good_lengths {z : ArgSplit} {w p} (g : z.Good w p) :
    z.lo.length ≤ w.length ∧ z.hi.length ≤ w.length := by
  cases g with
  | left => simp
  | right l => simp
  | sym b l h => simp; omega

def slide (z : ArgSplit) (d : Dir) : ArgSplit :=
  match d, z.center with
  | .N, _ | .R, .right | .L, .left => z
  | .R, c =>
    ⟨(z.hi.head?.map Mark.sym).getD .right,
     match c with | .sym b => b :: z.lo | _ => z.lo, z.hi.tail⟩
  | .L, c =>
    ⟨(z.lo.head?.map Mark.sym).getD .left,
     z.lo.tail, match c with | .sym b => b :: z.hi | _ => z.hi⟩

theorem good_slide {z : ArgSplit} {w p} (g : z.Good w p) (d) :
    (z.slide d).Good w (Mark.walk w p d) := by
  cases d with
  | N => exact g
  | R =>
    cases g with
    | left =>
      cases w with
      | nil => exact Good.right []
      | cons b h => exact Good.sym b [] h
    | right l => simpa [Mark.walk,slide] using Good.right l
    | sym b l h =>
      cases h with
      | nil =>
        simpa [Mark.walk,slide] using Good.right (b::l)
      | cons a h =>
        simpa [Mark.walk,slide] using Good.sym a (b::l) h
  | L =>
    cases g with
    | left => exact Good.left w
    | right l =>
      cases l with
      | nil => exact Good.left []
      | cons b l => simpa [Mark.walk,slide] using Good.sym b l []
    | sym b l h =>
      cases l with
      | nil => exact Good.left (b::h)
      | cons a l => simpa [Mark.walk,slide] using Good.sym a l (b::h)
end ArgSplit
end Fifths

end OAI
