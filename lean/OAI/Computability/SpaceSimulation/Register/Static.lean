import OAI.Computability.SpaceSimulation.Register.Arithmetic

namespace OAI

/-! Finite-case reasoning in the indexed complexity calculus. -/
namespace Fifths
namespace Comp
variable {X I Y : Type} {x : I → List X} {S a b : I → ℕ}

theorem divideCases [Fintype Y] (code : Y → ℕ) (inj : Function.Injective code)
    {w : I → Y} (r : Comp x S a (fun i => code (w i)))
    (h : ∀ y, Comp (fun i : {i // w i = y} => x i) (fun i => S i) (fun i => a i)
      (fun i => b i)) : Comp x S a b := by
  classical
  suffices g : ∀ l : Finset Y,
      Comp (fun i : {i // w i ∈ l} => x i) (fun i => S i) (fun i => a i) (fun i => b i) from
    (g Finset.univ).pull (fun i => ⟨i,Finset.mem_univ (w i)⟩)
  intro l
  induction l using Finset.induction_on with
  | empty =>
    let f := fun i : {i // w i ∈ (∅ : Finset Y)} => i.val
    exact (Comp.constant (r.pull f).source 0).congr (fun i => by have a := i.property; simp at a)
  | @insert y l m ih =>
    let f := fun i : {i // w i ∈ insert y l} => i.val
    have p := r.pull f
    let B (i : {i // w i ∈ insert y l}) := decide (code (w (f i)) = code y)
    refine (casesB (B := B) (p.eq (Comp.constant p.source (code y))) ?_ ?_)
    · exact (h y).pull (fun i : {i // B i = true} => ⟨f i.val,inj (of_decide_eq_true i.property)⟩)
    · exact ih.pull (fun i : {i // B i = false} => ⟨f i.val,by
        have g := Finset.mem_insert.mp i.val.property
        rcases g with g|g
        · have a := i.property
          simp [B,f,g] at a
        · exact g⟩)

theorem chooseCase [Fintype Y] (code : Y → ℕ) (inj : Function.Injective code) {w : I → Y}
    (p : I → Y → ℕ) (r : Comp x S a (fun i => code (w i)))
    (h : ∀ y, Comp x S a (fun i => p i y)) :
    Comp x S a (fun i => p i (w i)) := by
  refine divideCases code inj r ?_
  intro y
  exact ((h y).pull _).congr (fun i => congrArg (p i) i.property.symm)

end Comp
end Fifths

end OAI
