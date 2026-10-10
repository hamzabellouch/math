import OAI.Computability.SpaceSimulation.Register.Arithmetic

namespace OAI

namespace Fifths
namespace Scan

def all (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => all p n && p n

theorem all_iff (p : ℕ → Bool) (n) : all p n = true ↔ ∀ j < n, p j = true := by
  induction n with
  | zero => simp [all]
  | succ n ih =>
    rw [all, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨a,b⟩ j l
      by_cases e : j < n
      · exact a _ e
      · rw [show j = n by omega]
        exact b
    · exact fun a => ⟨fun j e => a _ (by omega), a n (by omega)⟩

def pick (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n+1 => if p n then n else pick p n

theorem pick_le (p : ℕ → Bool) (n) : pick p n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pick]; split <;> omega

theorem pick_spec (p : ℕ → Bool) (n) (e : ∃ j < n, p j = true) :
    pick p n < n ∧ p (pick p n) = true := by
  induction n with
  | zero => simp at e
  | succ n ih =>
    unfold pick
    split
    next h => exact ⟨by omega,h⟩
    next h =>
      suffices g : ∃ j < n, p j = true from ⟨by have := (ih g).1; omega,(ih g).2⟩
      obtain ⟨j,a,b⟩ := e
      refine ⟨j,?_,b⟩
      by_contra! v
      have l : j = n := by omega
      subst j
      contradiction

end Scan

namespace Comp
variable {X I : Type} {x : I → List X} {S a b : I → ℕ}

theorem scanAll (p : I → ℕ → Bool) (q : Comp x S a b)
    (h : ∀ e : Before b → ℕ, Comp (fun i => x i.1.1) (fun i => S i.1.1) e
       (fun i => a i.1.1) → Comp (fun i => x i.1.1) (fun i => S i.1.1) e (fun i => i.1.2)
       → Comp (fun i => x i.1.1) (fun i => S i.1.1) e
         (fun i => (p i.1.1 i.1.2).toNat)) :
    Comp x S a (fun i => (Scan.all (p i) (b i)).toNat) := by
  apply fold (fun i j => (Scan.all (p i) j).toNat) q
    (Comp.constant q.source 1)
  · exact (Fits.const _ 1).mono (fun _ => Bool.toNat_le _)
  · intro e i j r
    exact r.both (h e i j)

theorem scanPick (p : I → ℕ → Bool) (q : Comp x S a b)
    (h : ∀ e : Before b → ℕ, Comp (fun i => x i.1.1) (fun i => S i.1.1) e
       (fun i => a i.1.1) → Comp (fun i => x i.1.1) (fun i => S i.1.1) e (fun i => i.1.2)
       → Comp (fun i => x i.1.1) (fun i => S i.1.1) e
         (fun i => (p i.1.1 i.1.2).toNat)) :
    Comp x S a (fun i => Scan.pick (p i) (b i)) := by
  apply fold (fun i j => Scan.pick (p i) j) q
    (Comp.constant q.source 0)
  · let f : Through b → I := fun i => i.1.1
    exact (q.target.pull f).mono (fun i => (Scan.pick_le _ _).trans i.2)
  · intro e i j r
    exact (h e i j).iteB j r
end Comp
end Fifths

end OAI
