import Mathlib
import OAI.Computability.VertexCover.Machines.Lists

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                       
section

namespace VertexCover.Machine

abbrev natBits (n : ℕ) : List Bool := List.replicate n true
@[simp] theorem natBits_length (n : ℕ) : (natBits n).length = n := List.length_replicate

noncomputable def Poly.natSucc : Poly natBits natBits Nat.succ :=
  (Poly.cons true).realizes (fun _ => rfl)

noncomputable def Poly.natPred : Poly natBits natBits Nat.pred :=
  Poly.tail.realizes (fun n => by cases n <;> rfl)

noncomputable def Poly.natAdd : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1+p.2) :=
  Poly.append.encodeCongr (fun p => (natBits p.1,natBits p.2)) (fun _ => rfl)
    (fun _ => (List.replicate_add _ _ _).symm)

noncomputable def Poly.natZero : Poly natBits boolBits (fun n => decide (n=0)) :=
  Poly.isEmpty.encodeCongr natBits (fun _ => rfl) (fun n => by cases n <;> rfl)

noncomputable def Poly.natPositive : Poly natBits boolBits (fun n => decide (0<n)) :=
  (Poly.natZero.comp (Poly.bool Bool.not)).congr (fun n => by cases n <;> rfl)

namespace Iterate
variable {α : Type} (f : α → α)

def run : ℕ → α → α
  | 0,a => a
  | n+1,a => run n (f a)

def body : ℕ × α → Bool × (ℕ × α)
  | (0,a) => (false,(0,a))
  | (n+1,a) => (true,(n,f a))

noncomputable def bodyPoly (e : α → List Bool) (cf : Poly e e f) :
    Poly (prodBits natBits e) (flagBits (prodBits natBits e)) (body f) := by
  let cn := Poly.fst natBits e
  let ca := Poly.snd natBits e
  let test := cn.comp Poly.natPositive
  let next := (cn.comp Poly.natPred).pair (ca.comp cf)
  exact (test.flagPair (test.ite next (Poly.identity _))).congr (by
    intro ⟨n,a⟩; cases n <;> rfl)

theorem bounded (e : α → List Bool) (n : ℕ) (a : α) (B : ℕ)
    (bound : ∀ k l, k+l=n → (prodBits natBits e (l,run f k a)).length ≤ B) :
    BoundedRun (prodBits natBits e) (body f) B (n,a) (0,run f n a) (n+1) := by
  induction n generalizing a with
  | zero => exact .stop _ (bound 0 0 rfl) rfl
  | succ n ih =>
    exact .next _ _ _ (bound 0 (n+1) (Nat.zero_add _)) rfl (ih (f a) (by
      intro k l h
      exact bound (k+1) l (by omega)))
end Iterate

noncomputable def Poly.iterate {α : Type} (e : α → List Bool) {f : α → α}
    (cf : Poly e e f) (size : Polynomial ℕ)
    (bound : ∀ n a k l, k+l=n →
      (prodBits natBits e (l,Iterate.run f k a)).length ≤ size.eval (prodBits natBits e (n,a)).length) :
    Poly (prodBits natBits e) e (fun p : ℕ × α => Iterate.run f p.1 p.2) := by
  let result : ℕ × α → ℕ × α := fun p => (0,Iterate.run f p.1 p.2)
  let c := (Iterate.bodyPoly f e cf).loop result size (Polynomial.X+1) (by
    intro ⟨n,a⟩
    refine ⟨n+1,?_, Iterate.bounded f e n a _ (bound n a)⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, prodBits,
      pairBits_length,natBits_length]
    omega)
  exact (c.comp (Poly.snd natBits e)).congr (fun _ => rfl)

theorem iterate_pred (k n : ℕ) : Iterate.run Nat.pred k n = n-k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [Iterate.run,ih, Nat.pred_eq_sub_one]; omega

noncomputable def Poly.natSub : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1-p.2) := by
  let c := Poly.iterate natBits Poly.natPred Polynomial.X (by
    intro n a k l h
    simp only [Polynomial.eval_X,prodBits,pairBits_length,natBits_length,iterate_pred]
    omega)
  exact ((Poly.swap natBits natBits).comp c).congr (fun p => iterate_pred p.2 p.1)

noncomputable def Poly.natLE : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1≤p.2)) :=
  (Poly.natSub.comp Poly.natZero).congr (fun p => by
    simp only [Function.comp_apply,Nat.sub_eq_zero_iff_le])

noncomputable def Poly.bool₂ (f : Bool × Bool → Bool) :
    Poly (prodBits boolBits boolBits) boolBits f :=
  Poly.finite _ _ (by
    intro a b h
    simp only [prodBits,pairBits,boolBits,frame,List.cons_append,List.nil_append,List.cons.injEq] at h
    exact Prod.ext h.2.1 h.2.2.2.1) f

noncomputable def Poly.natBEq : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1=p.2)) := by
  let cr := (Poly.swap natBits natBits).comp Poly.natLE
  exact ((Poly.natLE.pair cr).comp (Poly.bool₂ (fun p => p.1 && p.2))).congr (by
    intro ⟨n,m⟩
    change (decide (n≤ m) && decide (m≤n)) = decide (n=m)
    simp only [← Bool.decide_and, Nat.le_antisymm_iff])

theorem iterate_add (k n a : ℕ) :
    Iterate.run (fun p : ℕ × ℕ => (p.1,p.1+p.2)) k (n,a) = (n,k*n+a) := by
  induction k generalizing a with
  | zero => simp [Iterate.run]
  | succ k ih => simp only [Iterate.run,ih]; congr 1; ring

noncomputable def Poly.natMul : Poly (prodBits natBits natBits) natBits
    (fun p : ℕ × ℕ => p.1*p.2) := by
  let e := prodBits natBits natBits
  let step := (Poly.fst natBits natBits).pair Poly.natAdd
  have bound (m : ℕ) (p : ℕ × ℕ) (k l : ℕ) (h : k+l=m) :
      (prodBits natBits e (l,Iterate.run (fun p : ℕ × ℕ => (p.1,p.1+p.2)) k p)).length ≤
        (10*(Polynomial.X+1)^2 : Polynomial ℕ).eval (prodBits natBits e (m,p)).length := by
    rcases p with ⟨n,a⟩
    simp only [iterate_add,prodBits,e,pairBits_length,natBits_length,Polynomial.eval_mul,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow,
      Polynomial.eval_ofNat]
    have hk : k≤ m := by omega
    have hkn := Nat.mul_le_mul_right n hk
    nlinarith [Nat.zero_le (m*n), Nat.zero_le ((m-n)^2)]
  let loop := Poly.iterate e step (10*(Polynomial.X+1)^2) bound
  let input := (Poly.fst natBits natBits).pair
    ((Poly.snd natBits natBits).pair (Poly.const _ natBits 0))
  exact ((input.comp loop).comp (Poly.snd natBits natBits)).congr (fun p => by
    simp only [Function.comp_apply,iterate_add,Nat.add_zero])

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
