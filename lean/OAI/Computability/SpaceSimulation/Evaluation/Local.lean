import OAI.Computability.SpaceSimulation.Evaluation.Interpolation

namespace OAI

namespace Fifths

namespace Modulus
variable (P : Modulus)

def packed (d : ℕ) (v : P.Vec) : ℕ :=
  Radix.pack P.n (fun i => (v i).val) (d+1)

theorem packed_lt (d : ℕ) (v : P.Vec) : P.packed d v < P.n^(d+1) :=
  Radix.pack_lt P.pos _ _ (fun _i _ => ZMod.val_lt _)
theorem get_packed (d : ℕ) (v : P.Vec) {i : ℕ} (p : i ≤ d) :
    Radix.get P.n (P.packed d v) i = (v i).val :=
  Radix.get_pack P.pos _ _ (fun _i _ => ZMod.val_lt _) (Nat.lt_succ_of_le p)

theorem aug_bounded (d u i : ℕ) : augBit d u i < 2 := by
  unfold augBit
  split_ifs <;> try omega
  exact Radix.get_lt (by omega) _ _
theorem aug_val (d u i : ℕ) : ((P.aug d u) i).val = augBit d u i :=
  ZMod.val_natCast_of_lt (lt_of_lt_of_le (aug_bounded ..) P.bound)
theorem fromAug (d u : ℕ) (h : u < 2^d) :
    Radix.pack 2 (fun i => ((P.aug d u) i).val) d = u := by
  refine Eq.trans (Radix.pack_congr (e := Radix.get 2 u) (fun j e => ?_)) (Radix.pack_get (by omega) u d h)
  rw [aug_val,augBit,ite_eq_left e]
end Modulus

namespace Comp
open Modulus
variable {I X : Type} {x : I → List X} {S a b d j : I → ℕ} {P : I → Modulus}

/-- Reduce repetition in local uniformity proofs. -/
abbrev ReComp {U : Type} (x : I → List X) (S : I → ℕ) (r : U → I) :=
  Comp (fun i => x (r i)) (fun i => S (r i))

variable (sizeD : Fits S (fun i => (P i).n^(d i+1)))
  (p : Comp x S a (fun i => (P i).n))
  (q : Comp x S a d)

include sizeD
theorem fitPowers (h : ∀ i, j i ≤ d i) :
    Fits S (fun i => (P i).n ^ j i) :=
  sizeD.mono (fun i => Nat.pow_le_pow_right (P i).pos (le_trans (h i) (by omega)))

theorem fitBitsD : Fits S (fun i => 2 ^ d i) :=
  (fitPowers sizeD (fun i => le_refl (d i))).mono
    (fun i => Nat.pow_le_pow_left (P i).bound _)

theorem fitPacked (v : ∀ i : I, (P i).Vec) :
    Fits S (fun i => (P i).packed (d i) (v i)) :=
  sizeD.mono (fun i => ((P i).packed_lt _ _).le)

include p
theorem coord {v : ∀ i : I, (P i).Vec}
    (w : Comp x S a (fun i => (P i).packed (d i) (v i)))
    (r : Comp x S a j) (h : ∀ i, j i ≤ d i) :
    Comp x S a (fun i => (v i (j i)).val) := by
  refine (digit p w r (fitPowers sizeD h)).congr ?_
  exact fun i => (P i).get_packed _ _ (h i)

include q
theorem wordBit (u : Comp x S a b) (l : Comp x S a j) (h : ∀ i, j i ≤ d i) :
    Comp x S a (fun i => augBit (d i) (b i) (j i)) := by
  have e : Comp x S a (fun i => Radix.get 2 (b i) (j i)) := by
    refine digit (Comp.constant p.source 2) u l ?_
    exact (fitBitsD sizeD).mono (fun i => Nat.pow_le_pow_right (by omega) (h i))
  exact ((l.lt q).iteB e ((l.eq q).iteB
    (Comp.constant p.source 1) (Comp.constant p.source 0))).congr (fun i => by simp [augBit])
theorem vector (v : ∀ i : I, (P i).Vec)
    (h : ∀ {U : Type} (r : U → I) {e j : U → ℕ}, ReComp x S r e (fun i => a (r i)) →
      ReComp x S r e j → (∀ i, j i ≤ d (r i)) → ReComp x S r e
      (fun i => (v (r i) (j i)).val)) :
    Comp x S a (fun i => (P i).packed (d i) (v i)) := by
  apply digits p q.plus1 sizeD (fun i => (P i).pos)
    (fun i j => (v i j).val) (fun i j _ => ZMod.val_lt _)
  intro e g f
  exact h (fun i : Before (fun i => d i+1) => i.1.1) g f (fun i => Nat.le_of_lt_succ i.2)

theorem basisAt (v : ∀ i : I, (P i).Vec) (u : Comp x S a b)
    (l : Comp x S a (fun i => (P i).packed (d i) (v i))) :
    Comp x S a (fun i => ((P i).basis (d i) (b i) (v i)).val) := by
  refine fieldProd (fun i => (P i).chooseCoord (d i) (b i) (v i)) p q ?_
  intro e g h
  let f : Before d → I := fun i => i.1.1
  let R : Before d → Modulus := fun i => P (f i)
  have t := g.trans (p.pull f)
  have o (i : Before d) : i.1.2 ≤ d (f i) := i.2.le
  have c := coord (P := R) (sizeD.pull f) t (g.trans (l.pull f)) h o
  have w := coord (P := R) (sizeD.pull f) t (g.trans (l.pull f))
    (g.trans (q.pull f)) (fun _ => le_rfl)
  have B := digit (Comp.constant g.source 2) (g.trans (u.pull f)) h
    (((fitBitsD sizeD).pull f).mono (fun i => Nat.pow_le_pow_right (by omega) (o i)))
  refine ((B.eq (Comp.constant g.source 1)).iteB c (fieldSub t w c)).congr (fun i => ?_)
  by_cases p : Radix.get 2 (b (f i)) i.1.2 = 1 <;> simp [chooseCoord,f] at p ⊢ <;>
    simp [p,f]

variable {v w : ∀ i : I, (P i).Vec}
theorem lookupOne (f : ∀ i : I, ℕ → (P i).K)
    (V : Comp x S a (fun i => (P i).packed (d i) (v i)))
    (o : ∀ {U : Type} (r : U → I) {e j : U → ℕ}, ReComp x S r e (fun i => a (r i)) →
      ReComp x S r e j → (∀ i, j i < 2^d (r i)) →
      ReComp x S r e (fun i => (f (r i) (j i)).val)) :
    Comp x S a (fun i => ((P i).extWord (d i) (f i) (v i)).val) := by
  let c := fun i => 2^d i
  have h : Comp x S a c := (Comp.constant p.source 2).pow q (fitBitsD sizeD)
  apply fieldSum (u := fun i j => (P i).basis (d i) j (v i) * f i j) p h
  intro e g l
  let k : Before c → I := fun i => i.1.1
  have t := g.trans (p.pull k)
  refine fieldMul (P := fun i => P (k i)) t
    (basisAt (sizeD.pull k) t (g.trans (q.pull k)) (fun i => v (k i)) l
     (g.trans (V.pull k))) (o k g l (fun i => i.2))

theorem lookupTwo (f : ∀ i : I, ℕ → ℕ → (P i).K)
    (V : Comp x S a (fun i => (P i).packed (d i) (v i)))
    (W : Comp x S a (fun i => (P i).packed (d i) (w i)))
    (o : ∀ {U : Type} (r : U → I) {e b j : U → ℕ}, ReComp x S r e (fun i => a (r i)) →
      ReComp x S r e b → ReComp x S r e j → (∀ i, b i < 2^d (r i)) →
      (∀ i, j i < 2^d (r i)) →
      ReComp x S r e (fun i => (f (r i) (b i) (j i)).val)) :
    Comp x S a (fun i => ((P i).extTwo (d i) (f i) (v i) (w i)).val) := by
  apply lookupOne sizeD p q (fun i j => (P i).extWord (d i) (f i j) (w i)) V
  intro U r e b g h l
  apply lookupOne (sizeD.pull r) (g.trans (p.pull r))
    (g.trans (q.pull r)) (fun i => f (r i) (b i)) (g.trans (W.pull r))
  intro T s n j a b z
  exact o (fun i => r (s i)) (a.trans (g.pull s)) (a.trans (h.pull s))
    b (fun i => l (s i)) z
end Comp
end Fifths

end OAI
