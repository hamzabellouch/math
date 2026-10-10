import OAI.Computability.MatchingCount.DivisionRoutine

namespace OAI

section

namespace BinaryMatching.StackCode.Poly
open BinaryMatching.Raw
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem rawNth [Inhabited β] (l : α → List β) (i : α → ℕ)
    (hl : Poly l) (hi : Poly i) : Poly (fun a => nth (l a) (i a)) :=
  comp _ _ (listGetD default) (pair l i hl hi)
@[fun_prop] theorem rawGet [Inhabited β] (m : α → Matrix β) (i j : α → ℕ)
    (hm : Poly m) (hi : Poly i) (hj : Poly j) : Poly (fun a => get (m a) (i a) (j a)) := by
  unfold Raw.get
  fun_prop
@[fun_prop] theorem rawMem (S : α → Cut) (i : α → ℕ) (hS : Poly S) (hi : Poly i) :
    Poly (fun a => mem (S a) (i a)) := by unfold mem; fun_prop
@[fun_prop] theorem rawTab [Inhabited α] (n : α → ℕ) (f : α×ℕ → β)
    (hn : Poly n) (hf : Poly f) : Poly (fun a => tab (n a) (fun i => f (a,i))) := by
  unfold tab
  apply mapWith _ _ (by fun_prop) hf
@[fun_prop] theorem rawMatrix [Inhabited α] (n : α → ℕ) (f : (α×ℕ)×ℕ → β)
    (hn : Poly n) (hf : Poly f) : Poly (fun a => matrix (n a) (fun i j => f ((a,i),j))) := by
  unfold matrix
  exact rawTab n (fun z => tab (n z.1) (fun j => f (z,j))) hn
    (rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf)

@[fun_prop] theorem rawEmpty : Poly empty := by unfold empty; fun_prop
@[fun_prop] theorem rawFull : Poly full := by unfold full; fun_prop
@[fun_prop] theorem rawInter : Poly (fun z : ℕ×(Cut×Cut) => inter z.1 z.2.1 z.2.2) := by
  unfold inter
  exact rawTab Prod.fst (fun z : (ℕ×(Cut×Cut))×ℕ => mem z.1.2.1 z.2 && mem z.1.2.2 z.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem rawCompl : Poly (fun z : ℕ×Cut => compl z.1 z.2) := by
  unfold Raw.compl
  exact rawTab Prod.fst (fun z : (ℕ×Cut)×ℕ => !mem z.1.2 z.2) (by fun_prop) (by fun_prop)
@[fun_prop] theorem rawCardinal : Poly cardinal := by
  unfold cardinal
  fun_prop

@[fun_prop] theorem uncurriedOptionMap [Inhabited α] [Inhabited β]
    (f : α×β → β) (hf : Poly f) :
    Poly (fun z : α×Option β => z.2.map (fun b => f (z.1,b))) := by
  have h : Poly (fun z : α×Option β => if z.2.isSome then
      Option.some (f (z.1,z.2.getD default)) else none) := by fun_prop
  exact h.congr (fun z => by cases z.2 <;> rfl)

end BinaryMatching.StackCode.Poly
end

end OAI
