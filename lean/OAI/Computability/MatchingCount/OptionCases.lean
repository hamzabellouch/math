import OAI.Computability.MatchingCount.RawSearchSize

namespace OAI

section

namespace BinaryMatching.StackCode.Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ] [Inhabited β]

theorem optionCasesWith (p : α → Option β) (f : α → γ) (g : α×β → γ)
    (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun a => match p a with | none => f a | Option.some b => g (a,b)) := by
  have h : Poly (fun a => if (p a).isSome then g (a,(p a).getD default) else f a) := by fun_prop
  exact h.congr (fun a => by cases p a <;> rfl)

theorem optionMapWith (p : α → Option β) (g : α×β → γ) (hp : Poly p) (hg : Poly g) :
    Poly (fun a => (p a).map (fun b => g (a,b))) := by
  have h := optionCasesWith p (fun _ => (none:Option γ))
    (fun z => Option.some (g z)) hp (by fun_prop) (by fun_prop)
  exact h.congr (fun a => by cases p a <;> rfl)
end BinaryMatching.StackCode.Poly
end

end OAI
