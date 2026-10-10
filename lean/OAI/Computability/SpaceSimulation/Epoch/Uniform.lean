import OAI.Computability.SpaceSimulation.Epoch.Nodes
import OAI.Computability.SpaceSimulation.Evaluation.Ready

namespace OAI

namespace Fifths.Tour
open Bin Modulus Fifths.Comp Radix
variable {I X U : Type}

attribute [local irreducible] Fifths.Modulus.chosen Fifths.Bin.pair
structure Runnable (D : I → Tour) (x : I → List X) (S cp : I → ℕ) : Prop where
  kOf : Comp x S cp (fun i => (D i).k)
  cOf : Comp x S cp (fun i => (D i).c)
  nOf : Comp x S cp (fun i => (D i).N)
  fitReg : Fits S (fun i => (D i).circuit.P.n ^ ((D i).width+1))
  initOf : Comp x S cp (fun i => (D i).init)
  tapeOf : ∀ {U : Type} (r : U → I) {a b : U → ℕ}, ReComp x S r a (fun i => cp (r i)) →
    ReComp x S r a b → ReComp x S r a (fun i => (D (r i)).tape (b i))
  selectOf : ∀ {U : Type} (r : U → I) {a b : U → ℕ}, ReComp x S r a (fun i => cp (r i)) →
    ReComp x S r a b → (∀ i, b i < (D (r i)).m) →
    ReComp x S r a (fun i => (D (r i)).sel (b i))
  visitOf : ∀ {U : Type} (r : U → I) {a b h : U → ℕ}, ReComp x S r a (fun i => cp (r i)) →
    ReComp x S r a b → ReComp x S r a h → (∀ i, b i < (D (r i)).m) →
    (∀ i, h i < (D (r i)).m^(D (r i)).b) →
    ReComp x S r a (fun i => let q := (D (r i)).visit (b i) (h i); Bin.pair q.1 q.2)

variable {D : I → Tour} {x : I → List X} {S cp : I → ℕ}
namespace Runnable

theorem strideOf (h : Runnable D x S cp) :
    Comp x S cp (fun i => (D i).stride) :=
  (h.nOf.add h.kOf).plus1
theorem totalOf (h : Runnable D x S cp) :
    Comp x S cp (fun i => (D i).total) :=
  h.kOf.plus1.mul h.strideOf
theorem bOf (h : Runnable D x S cp) :
    Comp x S cp (fun i => (D i).b) := h.kOf.mul h.kOf
theorem widthOf (h : Runnable D x S cp) :
    Comp x S cp (fun i => (D i).width) := h.cOf.mul h.bOf.plus1

theorem powFit (h : Runnable D x S cp) :
    Fits S (fun i => (D i).m ^ ((D i).b+1)) := by
  refine (fitBitsD h.fitReg).congr (fun i => (D i).powers _)

theorem powersFit (h : Runnable D x S cp) {u : U → ℕ} (r : U → I)
    (q : ∀ i, u i ≤ (D (r i)).b+1) :
    Fits (fun i => S (r i)) (fun i => (D (r i)).m ^ u i) :=
  (h.powFit.pull r).mono (fun i => Nat.pow_le_pow_right (D (r i)).m_pos (q i))

theorem mOf (h : Runnable D x S cp) :
    Comp x S cp (fun i => (D i).m) := by
  have g := powersFit h id (fun i => Nat.succ_le_succ (Nat.zero_le (D i).b))
  exact (Comp.constant h.cOf.source 2).pow h.cOf (g.congr (fun i => by simp [m]))

theorem last_bit (h : Runnable D x S cp) {r : U → I} {a b k : U → ℕ}
    (p : ReComp x S r a (fun i => cp (r i)))
    (q : ReComp x S r a b) (z : ReComp x S r a k) (g : ∀ i, k i ≤ (D (r i)).width+1) :
    ReComp x S r a (fun i => Modulus.augBit (D (r i)).width (b i) (k i)) := by
  have w := p.trans (h.widthOf.pull r)
  have f := (((fitBitsD h.fitReg).pull r).mul (Fits.const _ 2)).mono (g := fun i => 2^k i)
    (fun i => by
      simpa only [pow_succ] using Nat.pow_le_pow_right (show 0 < 2 by omega) (g i))
  have l := digit (Comp.constant p.source 2) q z f
  exact ((z.lt w).iteB l ((z.eq w).iteB
    (Comp.constant p.source 1) (Comp.constant p.source 0))).congr (fun i => by simp [augBit])

def replayCode (r : ℕ × Bool) : ℕ := Bin.pair r.1 r.2.toNat

theorem replay_comp (h : Runnable D x S cp)
    (g : ∀ i, (D i).FiniteWords)
    {r : U → I} {a b Z j n : U → ℕ}
    (p : ReComp x S r a (fun i => cp (r i)))
    (q : ReComp x S r a b) (z : ReComp x S r a Z)
    (v : ReComp x S r a j) (w : ReComp x S r a n)
    (l : ∀ i, n i ≤ (D (r i)).b) :
    ReComp x S r a (fun i => replayCode ((D (r i)).replay (j i) (Z i) (b i) (n i))) := by
  let R := fun (i : U) (y) => (D (r i)).replay (j i) (Z i) (b i) y
  have E (i : U) (m : ℕ) : (R i m).1 < (D (r i)).m^(D (r i)).b :=
    (D (r i)).replay_lt (g _) _ _ _ _
  have A := p.trans (h.mOf.pull r)
  have B := A.pow (p.trans (h.bOf.pull r)) (h.powersFit r (fun i => Nat.le_succ _))
  let f : U → ℕ → ℕ := fun i y => replayCode (R i y)
  refine fold f w ((q.mod B).pair (Comp.constant p.source 1)) ?_ ?_
  · let s : Through n → U := fun i => i.1.1
    exact ((B.target.pull s).mono (fun i => (E _ _).le)).pair
      ((Fits.const _ 1).mono (fun i => Bool.toNat_le _))
  intro e c₁ c₂ c₃
  let s : Before n → U := fun i => i.1.1
  let t : Before n → I := fun i => r (s i)
  let k := fun (i : Before n) => i.1.2
  have ap := c₁.trans (p.pull s)
  have az := c₁.trans (z.pull s)
  have bm := ap.trans (h.mOf.pull t)
  have u (i : Before n) : i.1.2+1 ≤ (D (t i)).b :=
    le_trans (Nat.succ_le_of_lt i.2) (l (s i))
  have b₁ := digit bm az c₂ (h.powersFit t (fun i => by
    have := u i; omega))
  have b₂ := digit bm az c₂.plus1 (h.powersFit t (fun i => Nat.le_succ_of_le (u i)))
  have d := h.selectOf t ap b₁ (fun i => get_lt (D (t i)).m_pos _ _)
  have o := h.visitOf t ap b₁ c₃.left
    (fun i => get_lt (D (t i)).m_pos _ _) (fun i => E (s i) (k i))
  let Y := fun i => get (D (t i)).m (Z (s i)) (k i)
  refine ((d.eq (c₁.trans (v.pull s))).iteB
    (o.right.pair (c₃.right.both (o.left.eq b₂))) c₃).congr ?_
  intro i
  change _ = replayCode ((D (t i)).replayStep (j (s i)) (Z (s i)) (k i) (R (s i) (k i)))
  dsimp only [replayStep]
  split -- determine which if (guard)
  · rename_i a
    rw [ite_eq_left (of_decide_eq_true a)]
    rfl
  · rename_i a
    rw [ite_eq_right (fun y => a (decide_eq_true y))]


section
variable (h : Runnable D x S cp)
    {r : U → I} {v : ∀ i, (D (r i)).Vertex} {a : U → ℕ}
    (p : ReComp x S r a (fun i => cp (r i)))
    (b : ReComp x S r a (fun i => (v i).val))
include h p

theorem makeV {e j : U → ℕ} (l : ReComp x S r a e) (q : ReComp x S r a j) :
    ReComp x S r a (fun i => ((D (r i)).mkV (e i) (j i)).val) :=
  ((l.mul (p.trans (h.strideOf.pull r))).add q).mod (p.trans (h.totalOf.pull r))

include b
theorem colOf :
    ReComp x S r a (fun i => (D (r i)).col (v i)) :=
  b.mod (p.trans (h.strideOf.pull r))
theorem epochOf :
    ReComp x S r a (fun i => (D (r i)).epoch (v i)) :=
  b.div (p.trans (h.strideOf.pull r))

theorem headOf :
    ReComp x S r a (fun i => ((D (r i)).header (v i)).val) := by
  have d := p.trans (h.kOf.pull r)
  have N := p.trans (h.nOf.pull r)
  have c := h.colOf p b
  have e := h.epochOf p b
  refine ((c.le N).iteB (h.makeV p e.minus1 (N.add d))
    (h.makeV p e (N.add (c.sub N).minus1))).congr ?_
  intro i
  by_cases q : (D (r i)).col (v i) ≤ (D (r i)).N <;> simp [hV,header,q,round]

theorem proposalOf {y f : U → ℕ} (l : ReComp x S r a f) (g : ReComp x S r a y) :
    ReComp x S r a (fun i => (D (r i)).proposal (v i) (f i) (y i)) := by
  have d := p.trans (h.kOf.pull r)
  have N := p.trans (h.nOf.pull r)
  have e := (((h.colOf p b).sub N).minus1.mul d).plus1
  have u := (p.trans (h.mOf.pull r)).pow e (h.powersFit r (fun i => ?_))
  · exact (l.mod u).add (u.mul g)
  exact Nat.add_le_add_right (Nat.mul_le_mul_right (D (r i)).k
    (Nat.le_trans (Nat.sub_le ((D (r i)).round (v i)) 1) ((D (r i)).round_le (v i)))) 1
end

theorem ready (h : Runnable D x S cp) (f : ∀ i, (D i).FiniteWords) :
    Circuit.Ready (fun i => (D i).circuit) x S cp := by
  refine ⟨h.widthOf,h.nOf,h.totalOf.target,h.fitReg,?_,?_,?_,?_⟩
  · intro U r a v p b
    have c := h.colOf p b
    have N := p.trans (h.nOf.pull r)
    have k := c.le N
    refine ⟨((h.epochOf p b).eq (Comp.constant c.source 0)).both k, ?_,h.headOf p b,?_⟩
    · exact (k.iteB (Comp.constant c.source 0)
        (p.trans (((h.cOf.mul h.kOf)).pull r))).congr (fun i => by simp [circuit,guesses,guessLength])
    · exact ((c.lt N).iteB (h.tapeOf r p c) (p.trans (h.initOf.pull r))).congr
        (fun i => by simp [circuit,firstOf])
  · intro U r a v k p b c _
    have d := h.epochOf p b
    have y := h.colOf p b
    have N := p.trans (h.nOf.pull r)
    refine ((y.lt N).iteB (h.makeV p d.minus1 y) ((y.eq N).iteB (h.headOf p b)
      (h.makeV p d c))).congr (fun i => ?_)
    by_cases l : (D (r i)).col (v i) < (D (r i)).N
    · simp [circuit,childrenOf,l]
    · by_cases m : (D (r i)).col (v i) = (D (r i)).N <;> simp [circuit,childrenOf,l,m]
  · intro U r a v z y u p b c d e l _ _
    have w := h.colOf p b
    have N := p.trans (h.nOf.pull r)
    have j := p.trans (h.bOf.pull r)
    have m := p.trans (h.mOf.pull r)
    have A := digit m e j (h.powersFit r (fun i => Nat.le_succ (D (r i)).b))
    have q := h.proposalOf p b e d
    have o := h.last_bit p A c l
    have s := h.last_bit p q c l
    exact ((w.lt N).iteB (Comp.constant w.source 1) ((w.eq N).iteB o s)).congr
      (fun i => by simp [circuit,offer])
  · intro U r a v z y k l w p b c d e g u m _ _ _ _
    have N := p.trans (h.nOf.pull r)
    have B := p.trans (h.bOf.pull r)
    have j := h.colOf p b
    have A := h.replay_comp f p u g j B (fun _ => le_refl _)
    have o := h.proposalOf p b g d
    have q := h.replay_comp f p u o e ((j.sub N).mul (p.trans (h.kOf.pull r)))
      (fun i => Nat.mul_le_mul_right (D (r i)).k ((D (r i)).round_le (v i)))
    have J := h.last_bit p A.left c m
    have T := Comp.constant (x := fun i => x (r i)) p.source 1
    exact ((j.lt N).iteB ((e.eq (Comp.constant p.source 0)).iteB J T)
      ((j.eq N).iteB T q.right)).congr (fun i => by simp [circuit,validAt,round])
end Runnable
end Fifths.Tour

end OAI
