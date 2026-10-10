import OAI.Computability.SpaceSimulation.Evaluation.Circuit
import OAI.Computability.SpaceSimulation.Register.Static

namespace OAI

/-! Uniform circuit presentation. In contrast to lookup-table evaluation
as a pure algebraic object, actual computation of a Boolean assignment's
function value is needed. -/
namespace Fifths
namespace Circuit
open Bin Modulus Fifths.Comp
variable {I X U : Type}

structure Ready (C : I → Circuit) (x : I → List X) (S cp : I → ℕ) : Prop where
  widthOf : Comp x S cp (fun i => (C i).width)
  countOf : Comp x S cp (fun i => (C i).count)
  fitNodes : Fits S (fun i => (C i).nodes)
  fitRegisters : Fits S (fun i => (C i).P.n ^ ((C i).width+1))
  nav : ∀ {U : Type} (r : U → I) {a} (v : ∀ i, (C (r i)).Node),
    ReComp x S r a (fun i => cp (r i)) →
    ReComp x S r a (fun i => (v i).val) →
    ReComp x S r a (fun i => ((C (r i)).base (v i)).toNat) ∧
    ReComp x S r a (fun i => (C (r i)).guessing (v i)) ∧
    ReComp x S r a (fun i => ((C (r i)).head (v i)).val) ∧
    ReComp x S r a (fun i => (C (r i)).first (v i))
  children : ∀ {U : Type} (r : U → I) {a} (v : ∀ i, (C (r i)).Node) k,
    ReComp x S r a (fun i => cp (r i)) →
    ReComp x S r a (fun i => (v i).val) → ReComp x S r a k →
    (∀ i, k i ≤ (C (r i)).count) →
    ReComp x S r a (fun i => ((C (r i)).child (v i) (k i)).val)
  proposeOf : ∀ {U : Type} (r : U → I) {a} (v : ∀ i, (C (r i)).Node) z y h,
    ReComp x S r a (fun i => cp (r i)) →
    ReComp x S r a (fun i => (v i).val) →
    ReComp x S r a z → ReComp x S r a y → ReComp x S r a h →
    (∀ i, z i ≤ (C (r i)).width+1) → (∀ i, y i ≤ 2^(C (r i)).width) →
    (∀ i, h i < 2^(C (r i)).width) →
    ReComp x S r a (fun i => (C (r i)).propose (v i) (z i) (y i) (h i))
  allowOf : ∀ {U : Type} (r : U → I) {a} (v : ∀ i, (C (r i)).Node) z y k h b,
    ReComp x S r a (fun i => cp (r i)) →
    ReComp x S r a (fun i => (v i).val) →
    ReComp x S r a z → ReComp x S r a y → ReComp x S r a k →
    ReComp x S r a h → ReComp x S r a b →
    (∀ i, z i ≤ (C (r i)).width+1) → (∀ i, y i ≤ 2^(C (r i)).width) →
    (∀ i, k i ≤ (C (r i)).count) →
    (∀ i, h i < 2^(C (r i)).width) → (∀ i, b i < 2^(C (r i)).width) →
    ReComp x S r a (fun i => (C (r i)).allows (v i) (z i) (y i) (k i) (h i) (b i))

section Independent
-- Small reusable constructions on represented values.
variable {C : I → Circuit} {x : I → List X} {S a : I → ℕ}

theorem slotMap (s : Slot → Slot) {q : I → Slot}
    (h : Comp x S a (fun i => (q i).val)) :
    Comp x S a (fun i => (s (q i)).val) :=
  chooseCase Fin.val Fin.val_injective (fun _ j => (s j).val) h
    (fun _j => Comp.constant h.source _)

theorem which {R : ∀ i, (C i).Pool}
    (p : Comp x S a (fun i => (C i).packPool (R i)))
    (s : Slot) : Comp x S a
    (fun i => (C i).P.packed (C i).width (R i s)) := by
  fin_cases s
  · exact p.left
  · exact p.right.left
  · exact p.right.right

theorem chooseSlot {R : ∀ i, (C i).Pool}
    (p : Comp x S a (fun i => (C i).packPool (R i)))
    {q : I → Slot}
    (h : Comp x S a (fun i => (q i).val)) :
    Comp x S a (fun i => (C i).P.packed (C i).width (R i (q i))) :=
  chooseCase Fin.val Fin.val_injective (fun i k => (C i).P.packed (C i).width (R i k)) h (which p)

theorem combinePool {R : ∀ i, (C i).Pool}
    (p : ∀ s : Slot, Comp x S a (fun i => (C i).P.packed (C i).width (R i s))) :
    Comp x S a (fun i => (C i).packPool (R i)) :=
  (p 0).pair ((p 1).pair (p 2))

variable (s : Fits S (fun i => (C i).P.n ^ ((C i).width+1)))
    (p : Comp x S a (fun i => (C i).P.n))
    (q : Comp x S a (fun i => (C i).width))
include s p q

theorem plusComp {R : ∀ i, (C i).Pool}
    (w : Comp x S a (fun i => (C i).packPool (R i))) {t : I → Slot}
    (v : Comp x S a (fun i => (t i).val)) {d : ∀ i, (C i).Vec}
    (h : Comp x S a (fun i => (C i).P.packed (C i).width (d i))) :
    Comp x S a (fun i => (C i).packPool ((C i).P.plus (R i) (t i) (d i))) := by
  apply combinePool
  intro k
  have e := which w k
  have l : Comp x S a (fun i => (C i).P.packed (C i).width
      (fun j => R i k j + d i j)) := by
    apply vector s p q _
    intro U r a j u c g
    let f := fun i => (C (r i)).P
    have x := u.trans (p.pull r)
    refine fieldAdd (P := f) x ?_ ?_
    · exact coord (s.pull r) x (u.trans (e.pull r)) c g
    · exact coord (s.pull r) x (u.trans (h.pull r)) c g
  refine ((v.eq (Comp.constant v.source k.val)).iteB l e).congr (fun i => ?_)
  by_cases g : k = t i
  · simp [← g,plus_at]
  · have f := Fin.val_injective.ne (Ne.symm g)
    simp [f,(C i).P.plus_other _ _ g]

theorem jump {b : ∀ i, (C i).F} (w : Comp x S a (fun i => (b i).val))
    {g : I → ℕ} (h : Comp x S a g) :
    Comp x S a (fun i => (C i).P.packed (C i).width
      ((C i).P.multiple (b i) ((C i).P.aug (C i).width (g i)))) := by
  apply vector s p q _
  intro U r a j e c m
  have x := e.trans (p.pull r)
  exact fieldMul x (e.trans (w.pull r)) (valCast x
    (wordBit (s.pull r) x (e.trans (q.pull r)) (e.trans (h.pull r)) c m))

theorem jumpOne {b : ∀ i, (C i).F} (w : Comp x S a (fun i => (b i).val))
    {g : I → ℕ} (h : Comp x S a g) :
    Comp x S a (fun i => (C i).P.packed (C i).width
      ((C i).P.spike (b i) (g i))) := by
  apply vector s p q _
  intro U r a j e c m
  have x := e.trans (p.pull r)
  refine ((c.eq (e.trans (h.pull r))).iteB (e.trans (w.pull r)) (valZero x)).congr
    (fun i => ?_)
  by_cases f : j i = g (r i) <;> simp [spike,f]

theorem formComp (k : Pc) {X' : ∀ i, (C i).Request} (w : Comp x S a
      (fun i => (C i).packX (X' i)))
    (r : Comp x S a (fun i => (C i).count))
    {s' z y j m : I → ℕ} {b g : ∀ i, (C i).F} (c₁ : Comp x S a s') (c₂ : Comp x S a z)
    (c₃ : Comp x S a y) (c₄ : Comp x S a j) (c₅ : Comp x S a m)
    (c₆ : Comp x S a (fun i => (b i).val)) (c₇ : Comp x S a (fun i => (g i).val)) :
    Comp x S a (fun i => (C i).packFrame ((C i).form (X' i) k (s' i) (z i) (y i)
      (j i) (m i) (b i) (g i))) :=
  w.pair ((Comp.constant w.source k.code).pair
    ((p.min c₁).pair ((q.plus1.min c₂).pair
      ((((Comp.constant p.source 2).pow q (fitBitsD s)).min c₃).pair
        ((r.min c₄).pair ((p.min c₅).pair (c₆.pair c₇)))))))
end Independent

namespace Ready
variable {C : I → Circuit} {x : I → List X} {S cp : I → ℕ}

theorem uniformDegree (c : Ready C x S cp) :
    Comp x S cp (fun i => (C i).outerDegree) :=
  c.countOf.plus1.mul c.widthOf

theorem modulusN (c : Ready C x S cp) :
    Comp x S cp (fun i => (C i).P.n) :=
  c.uniformDegree.chosenN

theorem frameSpace (c : Ready C x S cp) {r : U → I} (f : ∀ i, (C (r i)).Frame) :
    Fits (fun i => S (r i)) (fun i => (C (r i)).packFrame (f i)) := by
  have h₁ := c.fitNodes.pull r
  have h₂ := c.modulusN.target.pull r
  have h₃ := c.widthOf.target.pull r
  have h₄ := c.countOf.target.pull r
  have h₅ := (fitBitsD c.fitRegisters).pull r
  have w (g : ∀ i, (C (r i)).F) := fitElement (P := fun i => (C (r i)).P) h₂ g
  have q : Fits (fun i => S (r i)) (fun i => (C (r i)).packX (f i).x) :=
    ((Fits.const _ 3).mono (fun i => (f i).x.target.isLt.le)).pair
      ((h₁.mono (fun i => (f i).x.node.isLt.le)).pair (w _))
  refine q.pair (((Fits.const _ 7).mono ?_).pair
    ((h₂.mono ?_).pair (((h₃.add (Fits.const _ 1)).mono ?_).pair
       ((h₅.mono ?_).pair ((h₄.mono ?_).pair ((h₂.mono ?_).pair ((w _).pair (w _))))))))
  · intro i; cases (f i).pc <;> decide
  all_goals intro i
  · exact Nat.le_of_lt_succ (f i).s.isLt
  · exact Nat.le_of_lt_succ (f i).z.isLt
  · exact Nat.le_of_lt_succ (f i).y.isLt
  · exact Nat.le_of_lt_succ (f i).i.isLt
  · exact Nat.le_of_lt_succ (f i).r.isLt

theorem poolSpace (c : Ready C x S cp) {r : U → I} (R : ∀ i, (C (r i)).Pool) :
    Fits (fun i => S (r i)) (fun i => (C (r i)).packPool (R i)) := by
  have f (j : Slot) := fitPacked (P := fun i => (C (r i)).P)
    (c.fitRegisters.pull r) (fun i => R i j)
  exact (f 0).pair ((f 1).pair (f 2))
end Ready
end Circuit
end Fifths

end OAI
