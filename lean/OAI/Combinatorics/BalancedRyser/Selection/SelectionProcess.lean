import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import OAI.Combinatorics.BalancedRyser.Selection.Selection

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

structure Parameters where
  c : ℝ
  C : ℝ
  c₀ : ℝ
  a : ℝ

namespace Parameters

def Pstar (p : Parameters) : ℝ := 4 * p.C / p.c + 4

def alpha (p : Parameters) (q : ℕ) : ℝ := p.Pstar / q

def smin (p : Parameters) : ℝ := Real.exp (-6 * p.Pstar)

def Bstar (p : Parameters) : ℝ := 2 / (p.smin * p.c)

def rho (p : Parameters) : ℝ := p.c₀ * Real.exp (-6 * p.Bstar) / 4

def Admissible (p : Parameters) : Prop :=
  0 < p.c ∧ 0 < p.C ∧ 0 < p.c₀ ∧ p.c₀ ≤ 1 ∧
  0 < p.a ∧ p.a < min 1 (min (p.rho / 2) (p.c / (100 * (p.C + 1))))

def tailSlots (p : Parameters) (q : ℕ) : ℕ := Nat.ceil (p.a * q)

def lastMainTime (p : Parameters) (q n : ℕ) : ℕ := n - p.tailSlots q

def sizeScale (p : Parameters) (q t : ℕ) : ℝ := (1 - p.alpha q) ^ t

def degreeScale (p : Parameters) (q n t : ℕ) : ℝ :=
  p.sizeScale q t * (n - t : ℕ) / n

end Parameters

structure State (I V : Type*) where
  remaining : Finset I
  alive : Finset V
  recorded : I → Option V
  deriving Fintype

variable {I V : Type*} [Fintype I] [Fintype V]

def initialState : State I V := ⟨Finset.univ, Finset.univ, fun _ => none⟩

def domain (G : Input I V) (S : State I V) (i : I) : Finset V :=
  S.alive.filter (fun v => G.slot v = i)

def currentVertices (G : Input I V) (S : State I V) : Finset V :=
  S.alive.filter (fun v => G.slot v ∈ S.remaining)

def degree (G : Input I V) (S : State I V) (v : V) : ℕ :=
  ((neighbors G v) ∩ currentVertices G S).card

def hazard (G : Input I V) (S : State I V) (v : V) : ℝ :=
  (∑ i ∈ S.remaining, (((neighbors G v) ∩ domain G S i).card : ℝ) /
    (domain G S i).card) / S.remaining.card

def thinningRate (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V) (v : V) : ℝ :=
  if v ∈ currentVertices G S then
    (p.alpha q - hazard G S v) / (1 - hazard G S v)
  else 0

def Precheck (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V) : Prop :=
  S.remaining.Nonempty ∧ 0 ≤ p.alpha q ∧ p.alpha q < 1 ∧
  (∀ i ∈ S.remaining, (domain G S i).Nonempty ∧
    p.sizeScale q t * p.c * q / 2 ≤ ((domain G S i).card : ℝ)) ∧
  ∀ v ∈ currentVertices G S, hazard G S v ≤ p.alpha q

def drawWeight (G : Input I V) (S : State I V) (i : I) (w : V) : ℝ :=
  if i ∈ S.remaining ∧ w ∈ domain G S i then
    ((S.remaining.card : ℝ) * (domain G S i).card)⁻¹ else 0

def flagsWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V)
    (flags : V → Bool) : ℝ :=
  ∏ v, if flags v then thinningRate p q G S v else 1 - thinningRate p q G S v

def thinned (G : Input I V) (S : State I V) (w : V) (flags : V → Bool) : Finset V :=
  (currentVertices G S).filter (fun v => ¬ G.graph.Adj w v ∧ flags v = true)

def survivors (G : Input I V) (S : State I V) (w : V) (flags : V → Bool) : Finset V :=
  (currentVertices G S).filter (fun v => ¬ G.graph.Adj w v ∧ flags v = false)

def Postcheck (q : ℕ) (G : Input I V) (S : State I V) (w : V)
    (flags : V → Bool) : Prop :=
  (∀ i ∈ S.remaining, (((thinned G S w flags) ∩ domain G S i).card : ℝ) ≤
    (q : ℝ) ^ (1 / 8 : ℝ)) ∧
  (∀ v ∈ currentVertices G S,
    (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ))

def update (G : Input I V) (S : State I V) (i : I) (w : V)
    (flags : V → Bool) : State I V where
  remaining := S.remaining.erase i
  alive := (survivors G S w flags).filter (fun v => G.slot v ≠ i)
  recorded := Function.update S.recorded i (some w)

abbrev Noise (I V : Type*) := I × V × (V → Bool)

def noiseWeight (p : Parameters) (q : ℕ) (G : Input I V) (S : State I V)
    (r : Noise I V) : ℝ :=
  drawWeight G S r.1 r.2.1 * flagsWeight p q G S r.2.2

def performedResult (q : ℕ) (G : Input I V) (S : State I V) (r : Noise I V) :
    Option (State I V) :=
  if Postcheck q G S r.2.1 r.2.2 then some (update G S r.1 r.2.1 r.2.2) else none

def stepWeight (p : Parameters) (q t : ℕ) (G : Input I V) (S : State I V)
    (out : Option (State I V)) : ℝ :=
  if Precheck p q t G S then
    ∑ r : Noise I V, if performedResult q G S r = out then noiseWeight p q G S r else 0
  else if out = none then 1 else 0

def transitionWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Option (State I V)) : ℝ :=
  match before with
  | none => if out = none then 1 else 0
  | some S => stepWeight p q t G S out

def drawStepWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Option (State I V)) (draw : Option (Noise I V)) : ℝ :=
  match before with
  | none => if draw = none then 1 else 0
  | some S =>
      if Precheck p q t G S then
        match draw with
        | none => 0
        | some r => noiseWeight p q G S r
      else if draw = none then 1 else 0

def advance (q : ℕ) (G : Input I V) (before : Option (State I V))
    (draw : Option (Noise I V)) : Option (State I V) :=
  match before, draw with
  | some S, some r => performedResult q G S r
  | _, _ => none

abbrev Snapshot (I V : Type*) := Option (State I V) × Option (Noise I V)

def snapshotWeight (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) : ℝ :=
  if out.1 = advance q G before.1 out.2 then
    drawStepWeight p q t G before.1 out.2 else 0

def historyWeight (p : Parameters) (q : ℕ) (G : Input I V) :
    ℕ → Option (State I V) → ℝ
  | 0, out => if out = some initialState then 1 else 0
  | t + 1, out => ∑ before, historyWeight p q G t before * transitionWeight p q t G before out

def mainStageWeight (p : Parameters) (q : ℕ) (G : Input I V) : Option (State I V) → ℝ :=
  historyWeight p q G (p.lastMainTime q (Fintype.card I))

end
end Balanced.Selection.Process

end OAI
