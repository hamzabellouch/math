import OAI.Computability.MatchingCount.OrbitRoutine

namespace OAI

section

namespace BinaryMatching.StackCode

instance {α : Type} [Coding α] : Coding (Option α) := ⟨fun x => encode x.toList⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (Sum α β) :=
  ⟨fun x => match x with | .inl a => encode ([a],([]:List β)) | .inr b => encode (([]:List α),[b])⟩

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem some : Poly (Option.some : α → Option α) := by
  have h : Poly (fun a : α => [a]) := by fun_prop
  exact h.reindex Option.some id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionToList : Poly (Option.toList : Option α → List α) :=
  identity.reindex Option.toList Option.toList (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem optionGetD (a : α) : Poly (fun x : Option α => x.getD a) := by
  have h : Poly (fun x : Option α => x.toList.headD a) := comp _ _ (listHeadD a) optionToList
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionIsSome : Poly (Option.isSome : Option α → Bool) := by
  have h : Poly (fun x : Option α => !x.toList.isEmpty) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionMap [Inhabited α] (f : α → β) (hf : Poly f) :
    Poly (Option.map f) := by
  have h : Poly (fun x : Option α => x.toList.map f) := by fun_prop
  exact h.reindex (Option.map f) id (fun _ => rfl) (fun x => by cases x <;> rfl)

@[fun_prop] theorem optionElim [Inhabited α] (b : β) (f : α → β) (hf : Poly f) :
    Poly (fun x : Option α => x.elim b f) := by
  have h : Poly (fun x : Option α => if x.isSome then f (x.getD default) else b) := by fun_prop
  exact h.congr (fun x => by cases x <;> rfl)

@[fun_prop] theorem sumInl : Poly (Sum.inl : α → Sum α β) := by
  have h : Poly (fun a : α => ([a],([]:List β))) := by fun_prop
  exact h.reindex Sum.inl id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem sumInr : Poly (Sum.inr : β → Sum α β) := by
  have h : Poly (fun b : β => (([]:List α),[b])) := by fun_prop
  exact h.reindex Sum.inr id (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem sumCases [Inhabited α] [Inhabited β]
    (f : α → γ) (g : β → γ) (hf : Poly f) (hg : Poly g) :
    Poly (Sum.elim f g) := by
  let repr : Sum α β → List α×List β :=
    fun x => match x with | .inl a => ([a],[]) | .inr b => ([],[b])
  have h : Poly (fun z : List α×List β => if z.1.isEmpty then g (z.2.headD default)
      else f (z.1.headD default)) := by fun_prop
  exact h.reindex (Sum.elim f g) repr (fun x => by cases x <;> rfl)
    (fun x => by cases x <;> rfl)

end Poly
end BinaryMatching.StackCode
end

end OAI
