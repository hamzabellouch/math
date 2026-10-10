import OAI.Computability.SpaceSimulation.Register.Search

namespace OAI

/-!
Any characteristic works with the unambiguous selectors below; use a
prime field with a uniform binary computation of its modulus. Supplies
a bit-space certificate for field arithmetic and folds that retain only
residues.
-/
namespace Fifths

structure Modulus where
  n : ℕ
  prime : n.Prime

namespace Modulus
variable (P : Modulus)
instance : Fact P.n.Prime := ⟨P.prime⟩

abbrev K := ZMod P.n
theorem bound : 1 < P.n := P.prime.one_lt
theorem pos : 0 < P.n := P.prime.pos

def weight (d : ℕ) (u : P.K) : P.K :=
  -(u ^ (P.n - 1 - d))

-- Need a uniform computation yielding a modulus with Δ < p-1.
def divisorsOK (p : ℕ) (m : ℕ) : Bool :=
  !(decide (2 ≤ m) && decide (p % m = 0))

def isPrime (p : ℕ) : Bool :=
  decide (2 ≤ p) && Scan.all (divisorsOK p) p
theorem isPrime_iff (p : ℕ) : isPrime p = true ↔ p.Prime := by
  rw [isPrime, Bool.and_eq_true, Scan.all_iff, Nat.prime_def_lt']
  simp only [decide_eq_true_eq,divisorsOK,Bool.not_eq_true', Bool.and_eq_false_imp,
    decide_eq_false_iff_not]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i l r d
    exact h i r l (Nat.mod_eq_zero_of_dvd d)
  · intro h i l r d
    exact h i r l (Nat.dvd_of_mod_eq_zero d)

def rangeSize (d : ℕ) := 2*(d+1) + 1
def accepted (d p : ℕ) : Bool :=
  decide (d+1 < p) && isPrime p
theorem found (d : ℕ) :
    Scan.pick (accepted d) (rangeSize d) < rangeSize d ∧
      accepted d (Scan.pick (accepted d) (rangeSize d)) = true := by
  obtain ⟨p,a,l,h⟩ := Nat.exists_prime_lt_and_le_two_mul (d+1) (by omega)
  exact Scan.pick_spec _ _ ⟨p, by unfold rangeSize; omega, by simp [accepted,l,isPrime_iff,a]⟩

def chosen (d : ℕ) : Modulus :=
  let p := Scan.pick (accepted d) (rangeSize d)
  ⟨p, (isPrime_iff _).mp ((Bool.and_eq_true _ _).mp ((found d).2)).2⟩
theorem chosen_large (d : ℕ) : d+1 < (chosen d).n := by
  have h := (found d).2
  simp only [accepted,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h.1
theorem chosen_small (d : ℕ) : (chosen d).n < rangeSize d := (found d).1
end Modulus

namespace Comp
open Modulus
variable {I X : Type} {x : I → List X} {S a b d : I → ℕ}

theorem primality (h : Comp x S a b) :
    Comp x S a (fun i => (isPrime (b i)).toNat) := by
  refine ((Comp.constant h.source 2).le h).both (scanAll (fun i => divisorsOK (b i)) h ?_)
  intro e p r
  let f : Before b → I := fun i => i.1.1
  exact flip (((Comp.constant p.source 2).le r).both
    (((p.trans (h.pull f)).mod r).eq (Comp.constant p.source 0)))

theorem chosenN (h : Comp x S a d) :
    Comp x S a (fun i => (chosen (d i)).n) := by
  have r : Comp x S a (fun i => rangeSize (d i)) :=
    ((Comp.constant h.source 2).mul h.plus1).plus1
  refine scanPick (fun i => accepted (d i)) r ?_
  intro e i j
  let f : Before (fun i => rangeSize (d i)) → I := fun i => i.1.1
  exact (((i.trans (h.pull f)).plus1.lt j).both j.primality)

-- Field operations uniformly in the modulus. Even pow doesn't
-- materialize an ordinary integer power before reduction.
variable {P : I → Modulus} {v w : ∀ i : I, (P i).K}

theorem fitElement (h : Fits S (fun i => (P i).n)) (v : ∀ i : I, (P i).K) :
    Fits S (fun i => (v i).val) :=
  h.mono (fun _ => (ZMod.val_lt _).le)

theorem valCast (p : Comp x S a (fun i => (P i).n)) (q : Comp x S a b) :
    Comp x S a (fun i => (b i : (P i).K).val) :=
  (q.mod p).congr (fun _i => (ZMod.val_natCast _ _).symm)

theorem valZero (p : Comp x S a (fun i => (P i).n)) :
    Comp x S a (fun i => (0 : (P i).K).val) :=
  (Comp.constant p.source 0).congr (fun i => by simp)
theorem valOne (p : Comp x S a (fun i => (P i).n)) :
    Comp x S a (fun i => (1 : (P i).K).val) :=
  (p.valCast (Comp.constant p.source 1)).congr (fun i => by simp)

theorem fieldAdd (p : Comp x S a (fun i => (P i).n))
    (h : Comp x S a (fun i => (v i).val)) (q : Comp x S a (fun i => (w i).val)) :
    Comp x S a (fun i => (v i + w i).val) :=
  ((h.add q).mod p).congr (fun _i => (ZMod.val_add ..).symm)

theorem fieldNeg (p : Comp x S a (fun i => (P i).n))
    (h : Comp x S a (fun i => (v i).val)) :
    Comp x S a (fun i => (-v i).val) := by
  refine ((p.sub h).mod p).congr (fun i => ?_)
  by_cases e : v i = 0
  · simp [e]
  have : NeZero (v i) := ⟨e⟩
  have o : (v i).val ≠ 0 := by simpa using e
  have t := (P i).pos
  simp [ZMod.val_neg_of_ne_zero,Nat.mod_eq_of_lt (show
    (P i).n - (v i).val < (P i).n by omega)]

theorem fieldSub (p : Comp x S a (fun i => (P i).n))
    (h : Comp x S a (fun i => (v i).val)) (q : Comp x S a (fun i => (w i).val)) :
    Comp x S a (fun i => (v i - w i).val) :=
  (fieldAdd p h (fieldNeg p q)).congr (fun i => by simp [sub_eq_add_neg])

theorem fieldMul (p : Comp x S a (fun i => (P i).n))
    (h : Comp x S a (fun i => (v i).val)) (q : Comp x S a (fun i => (w i).val)) :
    Comp x S a (fun i => (v i * w i).val) :=
  ((h.mul q).mod p).congr (fun _i => (ZMod.val_mul ..).symm)

theorem fieldPow (p : Comp x S a (fun i => (P i).n))
    (h : Comp x S a (fun i => (v i).val)) (q : Comp x S a b) :
    Comp x S a (fun i => (v i ^ b i).val) := by
  refine fold (fun i j => (v i ^ j).val) q ((valOne p).congr (fun i => by simp)) ?_ ?_
  · let f : Through b → I := fun i => i.1.1
    exact fitElement (P := fun i => P (f i)) (p.target.pull f) _
  · intro e i j r
    let f : Before b → I := fun i => i.1.1
    exact (fieldMul (P := fun i => P (f i)) (i.trans (p.pull f)) r
      (i.trans (h.pull f))).congr (fun i => by simp [pow_succ,f])

-- Summation and product of field-valued procedures. Scratch reused.
open Finset
variable (u : ∀ i : I, ℕ → (P i).K)

theorem fieldSum (p : Comp x S a (fun i => (P i).n)) (q : Comp x S a b)
    (h : ∀ e : Before b → ℕ, Comp (fun i => x i.1.1) (fun i => S i.1.1) e
       (fun i => a i.1.1) → Comp (fun i => x i.1.1) (fun i => S i.1.1) e (fun i => i.1.2)
       → Comp (fun i => x i.1.1) (fun i => S i.1.1) e
         (fun i => (u i.1.1 i.1.2).val)) :
    Comp x S a (fun i => (∑ j ∈ range (b i), u i j).val) := by
  apply fold (fun i j => (∑ k ∈ range j, u i k).val) q
    ((valZero p).congr (fun i => by simp))
  · let f : Through b → I := fun i => i.1.1
    exact fitElement (P := fun i => P (f i)) (p.target.pull f) _
  · intro e i j r
    let f : Before b → I := fun i => i.1.1
    exact (fieldAdd (P := fun i => P (f i)) (i.trans (p.pull f)) r
      (h e i j)).congr (fun i => by simp [sum_range_succ])

theorem fieldProd (p : Comp x S a (fun i => (P i).n)) (q : Comp x S a b)
    (h : ∀ e : Before b → ℕ, Comp (fun i => x i.1.1) (fun i => S i.1.1) e
       (fun i => a i.1.1) → Comp (fun i => x i.1.1) (fun i => S i.1.1) e (fun i => i.1.2)
       → Comp (fun i => x i.1.1) (fun i => S i.1.1) e
         (fun i => (u i.1.1 i.1.2).val)) :
    Comp x S a (fun i => (∏ j ∈ range (b i), u i j).val) := by
  apply fold (fun i j => (∏ k ∈ range j, u i k).val) q
    ((valOne p).congr (fun i => by simp))
  · let f : Through b → I := fun i => i.1.1
    exact fitElement (P := fun i => P (f i)) (p.target.pull f) _
  · intro e i j r
    let f : Before b → I := fun i => i.1.1
    exact (fieldMul (P := fun i => P (f i)) (i.trans (p.pull f)) r
      (h e i j)).congr (fun i => by simp [prod_range_succ])

end Comp
end Fifths

end OAI
