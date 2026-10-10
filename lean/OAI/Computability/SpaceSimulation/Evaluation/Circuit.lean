import OAI.Computability.SpaceSimulation.Evaluation.Local
import OAI.Computability.SpaceSimulation.Register.Flow

namespace OAI

/-!
A specialized evaluator supporting the simulation's factored and ordinary
gates. Can treat the latter as special factored gates by allowing the
selector/test function at a coordinate z to depend on z, *including*
the extra coordinate d of augmented words.
-/
namespace Fifths

structure Circuit where
  width : ℕ
  count : ℕ
  nodes : ℕ
  base : Fin nodes → Bool
  -- `head` the distinguished child. All total (unused at base).
  head : Fin nodes → Fin nodes
  child : Fin nodes → ℕ → Fin nodes
  guessing : Fin nodes → ℕ
  first : Fin nodes → ℕ -- on base
  /-- arguments node, z, Y, H -/
  propose : Fin nodes → ℕ → ℕ → ℕ → ℕ
  /-- arguments node, z, Y, i, H, A -/
  allows : Fin nodes → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  semantic : Fin nodes → ℕ

abbrev Slot := Fin 3
namespace Slot
@[simp] def H (j : Slot) := j+1
@[simp] def A (j : Slot) := j+2
@[simp] theorem h_ne (j : Slot) : H j ≠ j := by fin_cases j <;> decide
@[simp] theorem a_ne (j : Slot) : A j ≠ j := by fin_cases j <;> decide
@[simp] theorem sep (j : Slot) : H j ≠ A j := by fin_cases j <;> decide
end Slot

namespace Modulus
variable (P : Modulus)

abbrev Pool := Slot → P.Vec

def plus (R : P.Pool) (t : Slot) (v : P.Vec) : P.Pool :=
  fun j i => if j=t then R j i + v i else R j i
def multiple (b : P.K) (v : P.Vec) : P.Vec := fun i => b * v i
def spike (b : P.K) (z : ℕ) : P.Vec := fun i => if i=z then b else 0

theorem plus_at (R : P.Pool) (t : Slot) (v : P.Vec) :
    P.plus R t v t = fun i => R t i + v i := by funext i; simp [plus]

theorem plus_other (R : P.Pool) {t j : Slot} (v : P.Vec) (h : j ≠ t) :
    P.plus R t v j = R j := by funext i; simp [plus,h]
theorem plus_zero (R : P.Pool) (t : Slot) :
    P.plus R t (fun _ => 0) = R := by
  ext j i
  simp [plus]

theorem plus_twice (R : P.Pool) (t : Slot) (v w : P.Vec) :
    P.plus (P.plus R t v) t w = P.plus R t (fun i => v i + w i) := by
  ext j i
  by_cases h : j = t <;> simp [plus,h,add_assoc]

theorem plus_comm (R : P.Pool) (t j : Slot) (v w : P.Vec) :
    P.plus (P.plus R t v) j w = P.plus (P.plus R j w) t v := by
  ext k i
  unfold plus; split_ifs <;> simp only [add_right_comm]

theorem plus_cancel (R : P.Pool) (t : Slot) (b : P.K) (v : P.Vec) :
    P.plus (P.plus R t (P.multiple b v)) t (P.multiple (-b) v) = R := by
  simp [plus_twice,multiple,plus_zero]

theorem plus_shift (R : P.Pool) (t : Slot) (b : P.K) (v : P.Vec) :
    P.plus R t (P.multiple b v) t = P.shift (R t) v b := by
  rw [plus_at]; rfl

end Modulus

namespace Circuit
variable (C : Circuit)
open Modulus Finset

abbrev Node := Fin C.nodes
def outerDegree := (C.count+1)*C.width
@[implicit_reducible] def P := Modulus.chosen C.outerDegree
abbrev F := C.P.K
abbrev Pool := C.P.Pool
abbrev Vec := C.P.Vec

/-- Last raw bit index is width-1; extra coordinate index width. -/
def value (v : C.Node) : C.Vec := C.P.aug C.width (C.semantic v)
def YCount (v : C.Node) := 2 ^ C.guessing v

def G (v : C.Node) (z y h : ℕ) : C.F := C.propose v z y h
def test (v : C.Node) (z y i h a : ℕ) : C.F := C.allows v z y i h a
def EG (v : C.Node) (z y : ℕ) (h : C.Vec) := C.P.extWord C.width (C.G v z y) h
def ET (v : C.Node) (z y i : ℕ) (h a : C.Vec) := C.P.extTwo C.width (C.test v z y i) h a

/-- Circuits are specification-only objects prior to uniformity hypotheses. -/
structure Good : Prop where
  bounded : ∀ v : C.Node, C.semantic v < 2^C.width
  small : ∀ v : C.Node, C.guessing v ≤ C.width
  leaf : ∀ v : C.Node, C.base v = true → C.semantic v = C.first v
  identityRule : ∀ v : C.Node, C.base v = false → ∀ z ≤ C.width,
    (∑ y ∈ range (C.YCount v), C.G v z y (C.semantic (C.head v)) *
      ∏ i ∈ range C.count, C.test v z y i (C.semantic (C.head v))
        (C.semantic (C.child v i))) = C.value v z

/-- A call changes only the requested slot, by the indicated multiple. -/
structure Request where
  node : C.Node
  scale : C.F
  target : Slot

namespace Request
variable {C}
def otherH (x : C.Request) (s : ℕ) : C.Request :=
  ⟨C.head x.node,s,Slot.H x.target⟩
def otherA (x : C.Request) (i r : ℕ) : C.Request :=
  ⟨C.child x.node i,r,Slot.A x.target⟩
def undo (x : C.Request) : C.Request := {x with scale := -x.scale}
def result (x : C.Request) (p : C.Pool) :=
  C.P.plus p x.target (C.P.multiple x.scale (C.value x.node))
end Request

inductive Pc
  | entry | outer | coord | guess | factor | sample | checkA
  deriving DecidableEq

instance : Fintype Pc :=
  ⟨{.entry, .outer, .coord, .guess, .factor, .sample, .checkA},
    by intro p; cases p <;> simp⟩

def Pc.code : Pc → ℕ
  | .entry => 0
  | .outer => 1
  | .coord => 2
  | .guess => 3
  | .factor => 4
  | .sample => 5
  | .checkA => 6

structure Frame where
  x : C.Request
  pc : Pc
  s : Fin (C.P.n+1)
  z : Fin (C.width+2)
  y : Fin (2^C.width+1)
  i : Fin (C.count+1)
  r : Fin (C.P.n+1)
  u : C.F
  w : C.F

-- Natural stages saturate if applied in arbitrary intermediate phases
-- at an out-of-range endpoint. On real path proofs will show bounds.
def clip (n : ℕ) (k : ℕ) : Fin (n+1) :=
  ⟨min n k,Nat.lt_succ_of_le (min_le_left _ _)⟩
@[simp] theorem clip_ok (n k : ℕ) (h : k ≤ n) :
    (clip n k).val = k := min_eq_right h

def form (x : C.Request) (pc : Pc)
    (s z y i r : ℕ) (u w : C.F) : C.Frame :=
  ⟨x,pc,clip _ s,clip _ z,clip _ y,clip _ i,clip _ r,u,w⟩
def fEntry (x : C.Request) : C.Frame := C.form x .entry 0 0 0 0 0 0 0
def fOuter (x : C.Request) (s : ℕ) : C.Frame := C.form x .outer s 0 0 0 0 0 0
def fCoord (x : C.Request) (s z : ℕ) : C.Frame := C.form x .coord s z 0 0 0 0 0
def fGuess (x : C.Request) (s z y : ℕ) : C.Frame := C.form x .guess s z y 0 0 0 0
def fFactor (x : C.Request) (s z y i : ℕ) (u : C.F) : C.Frame :=
  C.form x .factor s z y i 0 u 0
def fSample (x : C.Request) (s z y i r : ℕ) (u w : C.F) : C.Frame :=
  C.form x .sample s z y i r u w
def fCheck (x : C.Request) (s z y i r : ℕ) (u w : C.F) : C.Frame :=
  C.form x .checkA s z y i r u w

def amount (x : C.Request) (s : ℕ) (u : C.F) :=
  (x.scale * C.P.weight C.outerDegree (s : C.F))*u

/-- Each call pushes one measured frame. No intermediate vector
is scoped as scratch across pushes. After `checkA` release the
lookup work area; only one accumulated scalar is needed (plus u etc).
We compute w' (small) before the reverse push.
-/
def atPc (R : C.Pool) (f : C.Frame) (p : Pc) :
    C.Pool × FlowMove C.Frame :=
  let x := f.x
  let s : ℕ := f.s
  let z : ℕ := f.z
  let y : ℕ := f.y
  let i : ℕ := f.i
  let r : ℕ := f.r
  let u := f.u
  let w := f.w
  match p with
  | .entry =>
    if C.base x.node then
      (C.P.plus R x.target (C.P.multiple x.scale (C.P.aug C.width (C.first x.node))),
       .finish)
    else (R, .cont (C.fOuter x 0))
  | .outer =>
    if s < C.P.n then
      (R, .call (C.fEntry (x.otherH s)) (C.fCoord x s 0))
    else (R, .finish)
  | .coord =>
    if z < C.width+1 then (R, .cont (C.fGuess x s z 0))
    else (R, .call (C.fEntry (x.otherH s).undo) (C.fOuter x (s+1)))
  | .guess =>
    if y < C.YCount x.node then
      (R, .cont (C.fFactor x s z y 0 (C.EG x.node z y (R (Slot.H x.target)))))
    else (R, .cont (C.fCoord x s (z+1)))
  | .factor =>
    if i < C.count then (R, .cont (C.fSample x s z y i 0 u 0))
    else
      (C.P.plus R x.target (C.P.spike (C.amount x s u) z),
       .cont (C.fGuess x s z (y+1)))
  | .sample =>
    if r < C.P.n then
      (R, .call (C.fEntry (x.otherA i r)) (C.fCheck x s z y i r u w))
    else (R, .cont (C.fFactor x s z y (i+1) (u*w)))
  | .checkA =>
    let w' := w + C.P.weight C.width (r : C.F) *
      (C.ET x.node z y i (R (Slot.H x.target)) (R (Slot.A x.target)))
    (R, .call (C.fEntry (x.otherA i r).undo) (C.fSample x s z y i (r+1) u w'))

open Bin
def packPool (R : C.Pool) := pair (C.P.packed C.width (R 0))
  (pair (C.P.packed C.width (R 1)) (C.P.packed C.width (R 2)))

def packX (x : C.Request) := pair x.target.val (pair x.node.val x.scale.val)

def packFrame (f : C.Frame) :=
  pair (C.packX f.x) (pair f.pc.code (pair f.s.val (pair f.z.val (pair f.y.val
    (pair f.i.val (pair f.r.val (pair f.u.val f.w.val)))))))

def flow : Flow :=
  ⟨C.Pool,C.Frame,C.packPool,C.packFrame,fun R f => C.atPc R f f.pc⟩

/-- Uniform fee estimates intentionally very loose. -/
def price (g : ℕ) :=
  100 * ((((((1+C.nodes.size)+C.width.size)+C.count.size)+C.P.n.size)+g)+1)

structure Meter (coins : C.Node → ℕ) : Prop where
  cheap : ∀ v : C.Node, C.base v = false →
    coins (C.head v) + C.price 0 ≤ coins v
  expensive : ∀ v : C.Node, C.base v = false → ∀ i < C.count,
    coins (C.child v i) + C.price (C.guessing v) ≤ coins v

theorem price_bounds (f : C.Frame) (g : ℕ) (h : f.y.val.size ≤ g+1) :
    C.flow.fee f ≤ C.price g := by
  have a : f.pc.code.size ≤ 4 := by cases f.pc <;> decide
  have b : f.x.target.val.size ≤ 2 := by
    have := Nat.size_le_size f.x.target.isLt.le
    exact this.trans (show Nat.size 3 ≤ 2 by decide)
  have c := Nat.size_le_size f.x.node.isLt.le
  have p := Nat.size_le_size (show f.i.val ≤ C.count from Nat.le_of_lt_succ f.i.isLt)
  have r := Nat.size_le_size (show f.s.val ≤ C.P.n from Nat.le_of_lt_succ f.s.isLt)
  have q := Nat.size_le_size (show f.r.val ≤ C.P.n from Nat.le_of_lt_succ f.r.isLt)
  have z := Nat.size_le_size (show f.z.val ≤ C.width+1 from Nat.le_of_lt_succ f.z.isLt)
  have e := Bin.succ_size C.width
  have l (x : C.F) : x.val.size ≤ C.P.n.size := Nat.size_le_size (ZMod.val_lt x).le
  have l₁ := l f.x.scale
  have l₂ := l f.u
  have l₃ := l f.w
  change 2*(C.packFrame f).size + 1 ≤ C.price g
  simp only [packFrame,packX,pair_size,price]
  omega
end Circuit
end Fifths

end OAI
